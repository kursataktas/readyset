use std::panic::AssertUnwindSafe;

use chrono::DateTime;
use mysql_async::prelude::Queryable;
use mysql_async::Params;
use mysql_common::{Row, Value};
use nom_sql::{Dialect, DialectDisplay, EnumVariants, SqlType, SqlTypeArbitraryOptions};
use proptest::arbitrary::any;
use proptest::collection::vec;
use proptest::prop_oneof;
use proptest::sample::{select, size_range};
use proptest::strategy::{Just, Strategy};
use proptest::string::string_regex;
use proptest::test_runner::Config as ProptestConfig;
use readyset_client_test_helpers::mysql_helpers::MySQLAdapter;
use readyset_client_test_helpers::{mysql_helpers, TestBuilder};
use readyset_util::arbitrary::{
    arbitrary_decimal_bytes_with_digits, arbitrary_json, arbitrary_naive_date_in_range,
    arbitrary_naive_time_with_seconds_fraction,
};
use readyset_util::eventually;
use serial_test::serial;
use test_strategy::proptest;
use test_utils::slow;

fn round_trip_mysql_type(sql_type: SqlType, value: Value) {
    readyset_tracing::init_test_logging();
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(round_trip_mysql_type_inner(sql_type, value))
}

async fn round_trip_mysql_type_inner(sql_type: SqlType, value: Value) {
    let upstream_opts = mysql_helpers::upstream_config().db_name(Some("round_trip_mysql_types"));
    mysql_helpers::recreate_database("round_trip_mysql_types").await;

    let mut upstream_conn = mysql_async::Conn::new(upstream_opts).await.unwrap();

    // Allow zero dates, leaving remaining default flags (as of 8.0/8.4).
    upstream_conn.query_drop("set sql_mode = 'ONLY_FULL_GROUP_BY,STRICT_TRANS_TABLES,ERROR_FOR_DIVISION_BY_ZERO,NO_ENGINE_SUBSTITUTION'").await.unwrap();

    upstream_conn
        .query_drop(format!(
            "CREATE TABLE snapshot (value {})",
            sql_type.display(Dialect::MySQL)
        ))
        .await
        .unwrap();
    upstream_conn
        .exec_drop(
            "INSERT INTO snapshot (value) VALUES (?)",
            Params::from(vec![&value]),
        )
        .await
        .unwrap();

    // We use the value the upstream actually stores for subsequent lookups, in case it trims or
    // pads the value.
    let upstream_rows: Vec<Row> = upstream_conn
        .exec(
            "SELECT * FROM snapshot WHERE value = ?",
            Params::from(vec![&value]),
        )
        .await
        .unwrap();

    // Not all values work for lookups; e.g. spaces in a CHAR column.
    if upstream_rows.is_empty() {
        return;
    }

    // We use the value the upstream actually stores for subsequent lookups, in case it trims or
    // pads the value.
    let upstream_val = &upstream_rows[0][0];

    // Snapshot & check result
    let (rs_opts, _rs_handle, shutdown_tx) = TestBuilder::default()
        .recreate_database(false)
        .fallback_db("round_trip_mysql_types".to_string())
        .build::<MySQLAdapter>()
        .await;
    let mut rs_conn = mysql_async::Conn::new(rs_opts).await.unwrap();

    // Check the result of snapshot on Readyset
    eventually!(attempts: 5, run_test: {
        let rs_rows: Vec<Row> = rs_conn
            .exec(
                "SELECT * FROM snapshot WHERE value = ?",
                Params::from(vec![upstream_val]),
            )
            .await
            .unwrap();
        AssertUnwindSafe(move || rs_rows)
    }, then_assert: |results| {
        let rs_rows = results();
        assert_eq!(&rs_rows[0][0], upstream_val);
    });

    // Replicate & check result
    upstream_conn
        .query_drop(format!(
            "CREATE TABLE replicate (value {})",
            sql_type.display(Dialect::MySQL)
        ))
        .await
        .unwrap();
    upstream_conn
        .exec_drop(
            "INSERT INTO replicate (value) VALUES (?)",
            Params::from(vec![&value]),
        )
        .await
        .unwrap();
    let replicated_upstream_rows: Vec<Row> = upstream_conn
        .exec(
            "SELECT * FROM replicate WHERE value = ?",
            Params::from(vec![&value]),
        )
        .await
        .unwrap();

    let replicated_upstream_val = &replicated_upstream_rows[0][0];
    assert_eq!(replicated_upstream_val, upstream_val);

    // Check the result of streaming replication on Readyset
    eventually!(attempts: 5, run_test: {
        let replicated_rs_rows: Vec<Row> = rs_conn
            .exec(
                "SELECT * FROM replicate WHERE value = ?",
                Params::from(vec![upstream_val]),
            )
            .await
            .unwrap();
        AssertUnwindSafe(move || replicated_rs_rows)
    }, then_assert: |results| {
        let replicated_rs_rows = results();
        assert_eq!(&replicated_rs_rows[0][0], upstream_val);
    });

    shutdown_tx.shutdown().await;
}

fn arbitrary_mysql_value_for_type(sql_type: SqlType) -> impl Strategy<Value = Value> {
    match sql_type {
        SqlType::Citext
        | SqlType::Serial
        | SqlType::BigSerial
        | SqlType::ByteArray
        | SqlType::Array(_)
        | SqlType::Inet
        | SqlType::Int2
        | SqlType::Int4
        | SqlType::Int8
        | SqlType::MacAddr
        | SqlType::Other(..)
        | SqlType::Uuid
        | SqlType::QuotedChar
        | SqlType::Interval { .. }
        | SqlType::Jsonb => {
            panic!("Type not supported by MySQL: {sql_type:?}")
        }
        SqlType::TimestampTz => Just(Value::Int(0))
            .prop_filter("not yet implemented", |_| false)
            .boxed(),
        SqlType::Date => arbitrary_naive_date_in_range(1000..=9999)
            .prop_map(|date| date.into())
            .boxed(),
        SqlType::Time => arbitrary_naive_time_with_seconds_fraction()
            .prop_map(|time| time.into())
            .boxed(),
        SqlType::DateTime(_) => (
            arbitrary_naive_date_in_range(1000..=9999),
            arbitrary_naive_time_with_seconds_fraction(),
        )
            .prop_map(|(date, time)| date.and_time(time).to_string().into())
            .boxed(),
        // Max timestamp corresponds to MySQL docs: 2038-01-19 03:14:07
        // TODO(mvzink): If run on machine with non-UTC TZ/offset, I believe this will error
        // converting past this bound
        SqlType::Timestamp => (1..=2147483647i64, 0..=1_000_000_000u32)
            .prop_map(|(secs, nsecs)| {
                DateTime::from_timestamp(secs, nsecs)
                    .unwrap_or_else(|| panic!("out of range ({secs}, {nsecs})"))
                    .naive_utc()
                    .to_string()
                    .into()
            })
            .boxed(),
        SqlType::Binary(len) => vec(any::<u8>(), 0..(len.unwrap_or(255) as usize))
            .prop_map(Value::Bytes)
            .boxed(),
        SqlType::VarBinary(len) => vec(any::<u8>(), 0..(len as usize))
            .prop_map(Value::Bytes)
            .boxed(),
        SqlType::TinyBlob | SqlType::Blob | SqlType::MediumBlob | SqlType::LongBlob => {
            vec(any::<u8>(), 0..255).prop_map(Value::Bytes).boxed()
        }
        SqlType::TinyText | SqlType::Text | SqlType::MediumText | SqlType::LongText => {
            any::<String>()
                .prop_map(|s| Value::Bytes(s.into_bytes()))
                .boxed()
        }
        SqlType::Char(len) | SqlType::VarChar(len) => {
            string_regex(&format!("\\PC{{0,{}}}", len.unwrap_or(1)))
                .expect("Should produce valid regex")
                .prop_map(|s| Value::Bytes(s.into_bytes()))
                .boxed()
        }
        SqlType::Bit(/* TODO */ len) | SqlType::VarBit(len) => prop_oneof![
            any::<u64>().prop_map(Value::UInt),
            vec(any::<u8>(), 0..(len.unwrap_or(255) as usize)).prop_map(Value::Bytes)
        ]
        .boxed(),
        SqlType::Bool => (0..=1i64).prop_map(Value::Int).boxed(),
        SqlType::Float => any::<f32>().prop_map(Value::Float).boxed(),
        SqlType::Double | SqlType::Real => any::<f64>().prop_map(Value::Double).boxed(),
        SqlType::TinyInt(_) => any::<i8>().prop_map(|i| Value::Int(i as i64)).boxed(),
        SqlType::SmallInt(_) => any::<i16>().prop_map(|i| Value::Int(i as i64)).boxed(),
        SqlType::MediumInt(_) => ((-1i64 << 23)..(1i64 << 23)).prop_map(Value::Int).boxed(),
        SqlType::Int(_) => any::<i32>().prop_map(|i| Value::Int(i as i64)).boxed(),
        SqlType::BigInt(_) => any::<i64>().prop_map(Value::Int).boxed(),
        SqlType::UnsignedTinyInt(_) => any::<u8>().prop_map(|i| Value::UInt(i as u64)).boxed(),
        SqlType::UnsignedSmallInt(_) => any::<u16>().prop_map(|i| Value::UInt(i as u64)).boxed(),
        SqlType::UnsignedMediumInt(_) => (0..(1u64 << 24)).prop_map(Value::UInt).boxed(),
        SqlType::UnsignedInt(_) => any::<u32>().prop_map(|i| Value::UInt(i as u64)).boxed(),
        SqlType::UnsignedBigInt(_) => any::<u64>().prop_map(Value::UInt).boxed(),
        SqlType::Decimal(m, d) => arbitrary_decimal_bytes_with_digits(m.into(), d)
            .prop_map(Value::Bytes)
            .boxed(),
        SqlType::Numeric(maybe_m_d) => {
            let (m, maybe_d) = maybe_m_d.unwrap_or((10, None));
            let d = maybe_d.unwrap_or(0);
            arbitrary_decimal_bytes_with_digits(m, d)
                .prop_map(Value::Bytes)
                .boxed()
        }
        SqlType::Json => arbitrary_json().prop_map(|json| json.into()).boxed(),
        SqlType::Enum(variants) => select(variants.iter().cloned().collect::<Vec<_>>())
            .prop_map(|variant: String| variant.into())
            .boxed(),
    }
}

#[proptest(ProptestConfig::default(), max_shrink_time = 120_000)]
#[serial]
#[slow]
#[ignore = "WIP REA-4598"]
fn round_trip_mysql_type_arbitrary(
    #[strategy(SqlType::arbitrary_with(SqlTypeArbitraryOptions {
        dialect: Some(Dialect::MySQL),
        generate_arrays: false,
        generate_json: true,
        generate_other: false,
    }))]
    sql_type: SqlType,
    #[strategy(arbitrary_mysql_value_for_type(#sql_type))] value: Value,
) {
    round_trip_mysql_type(sql_type, value)
}

#[proptest(ProptestConfig::default(), max_shrink_time = 120_000)]
#[serial]
#[slow]
#[ignore = "WIP REA-4598"]
fn round_trip_mysql_type_arbitrary_enum(
    #[strategy(EnumVariants::arbitrary_with(("\\PC{0,255}", size_range(1..100))).prop_map(|variants| SqlType::Enum(variants)))]
    sql_type: SqlType,
    #[strategy(arbitrary_mysql_value_for_type(#sql_type))] value: Value,
) {
    round_trip_mysql_type(sql_type, value)
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_enum() {
    round_trip_mysql_type(
        SqlType::from_enum_variants(["foo".into(), "bar".into()]),
        Value::Bytes("foo".as_bytes().to_vec()),
    );
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_tinyint_positive() {
    round_trip_mysql_type(SqlType::TinyInt(None), Value::Int(1));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_tinyint_negative() {
    round_trip_mysql_type(SqlType::TinyInt(None), Value::Int(-1));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_mediumint_positive() {
    round_trip_mysql_type(SqlType::MediumInt(None), Value::Int(1));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_mediumint_unsigned_positive() {
    round_trip_mysql_type(SqlType::UnsignedMediumInt(None), Value::UInt(1));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_mediumint_negative() {
    round_trip_mysql_type(SqlType::MediumInt(None), Value::Int(-1));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_mediumint_unsigned_positive_large_sending_signed() {
    round_trip_mysql_type(SqlType::UnsignedMediumInt(None), Value::Int(8388608));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_mediumint_unsigned_positive_large_sending_unsigned() {
    round_trip_mysql_type(SqlType::UnsignedMediumInt(None), Value::UInt(8388608));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_decimal() {
    round_trip_mysql_type(SqlType::Decimal(10, 5), Value::Bytes("-0.5".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_decimal_no_preceding_digits() {
    round_trip_mysql_type(SqlType::Decimal(10, 5), Value::Bytes(".5".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_decimal_no_preceding_digits_negative() {
    round_trip_mysql_type(SqlType::Decimal(10, 5), Value::Bytes("-.5".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_zero_length() {
    round_trip_mysql_type(SqlType::Char(Some(0)), Value::Bytes("".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_1_length_empty() {
    round_trip_mysql_type(SqlType::Char(Some(1)), Value::Bytes("".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_64_length_empty() {
    round_trip_mysql_type(SqlType::Char(Some(64)), Value::Bytes("".into()))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_63_length_empty() {
    round_trip_mysql_type(SqlType::Char(Some(63)), Value::Bytes("".into()))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_46_length_nonempty() {
    round_trip_mysql_type(SqlType::Char(Some(46)), Value::Bytes("d".into()));
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_255_length_empty() {
    round_trip_mysql_type(SqlType::Char(Some(255)), Value::Bytes("".into()))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_64_length_nonempty() {
    round_trip_mysql_type(SqlType::Char(Some(64)), Value::Bytes("d".into()))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_char_255_length_nonempty() {
    round_trip_mysql_type(SqlType::Char(Some(255)), Value::Bytes("d".into()))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_bigint_high() {
    round_trip_mysql_type(
        SqlType::UnsignedBigInt(None),
        Value::UInt(9223372036854775808),
    )
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_date() {
    round_trip_mysql_type(SqlType::Date, Value::Date(2024, 2, 4, 0, 0, 0, 0))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_date_zero() {
    round_trip_mysql_type(SqlType::Date, Value::Date(0, 0, 0, 0, 0, 0, 0))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_datetime() {
    round_trip_mysql_type(SqlType::DateTime(None), Value::Date(2024, 2, 4, 0, 0, 0, 0))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_datetime_zero() {
    round_trip_mysql_type(SqlType::DateTime(None), Value::Date(0, 0, 0, 0, 0, 0, 0))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_timestamp_zero() {
    round_trip_mysql_type(SqlType::Timestamp, Value::Date(0, 0, 0, 0, 0, 0, 0))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_bool_one_unsigned() {
    round_trip_mysql_type(SqlType::Bool, Value::UInt(1))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_bool_one_signed() {
    round_trip_mysql_type(SqlType::Bool, Value::Int(1))
}

#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_bool_zero_unsigned() {
    round_trip_mysql_type(SqlType::Bool, Value::UInt(0))
}
#[test]
#[serial]
#[slow]
fn round_trip_mysql_type_regressions_bool_zero_signed() {
    round_trip_mysql_type(SqlType::Bool, Value::Int(0))
}
