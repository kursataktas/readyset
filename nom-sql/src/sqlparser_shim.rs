//! A shim to replace

use core::str;

use nom::branch::alt;
use nom::combinator::map;
use nom::error::ErrorKind;
use nom::AsBytes;
use nom_locate::LocatedSpan;

use crate::create::create_cached_query;
use crate::drop::{drop_all_caches, drop_all_proxied_queries, drop_cached_query};
use crate::explain::explain_statement;
use crate::literal::dollarsign_placeholder;
use crate::order::NullOrder;
use crate::select::SelectStatement;
use crate::show::{FilterPredicate, ShowStatement, Tables};
use crate::{
    BinaryOperator, CaseWhenBranch, Column, Dialect, Expr, FieldDefinitionExpr, FieldReference,
    GroupByClause, ItemPlaceholder, JoinClause, JoinConstraint, JoinOperator, LimitClause,
    LimitValue, Literal, NomSqlError, NomSqlResult, OrderBy, OrderClause, OrderType, Relation,
    SqlIdentifier, SqlQuery, TableExpr, TableExprInner,
};

/// Convert sqlparser-rs's AST to nom-sql's.
///
/// This only attempts to convert statements that the mysql client sends on startup so we need to at least to not die
/// (but see the TODO below), plus `SELECT` statements.
///
/// TODO: This should be `TryFrom`, but I wanted to hard error with clickable line numbers while hacking
impl From<sqlparser::ast::Statement> for SqlQuery {
    fn from(value: sqlparser::ast::Statement) -> Self {
        use sqlparser::ast::Statement::*;
        match value {
            Query(query) => (*query).into(),
            // This is kind of crazy; neither sqlparser-rs nor nom-sql actually support MySQL's `SHOW DATABASES` syntax
            ShowVariable { ref variable } => {
                if variable
                    .iter()
                    .map(|ident| &ident.value)
                    .collect::<Vec<_>>()
                    == vec!["databases"]
                {
                    Self::Show(ShowStatement::Databases)
                } else {
                    unimplemented!("unsupported ShowVariables {value:?}")
                }
            }
            ShowTables {
                full,
                db_name,
                filter,
                ..
            } => Self::Show(ShowStatement::Tables(Tables {
                full,
                from_db: db_name.map(|ident| ident.value),
                filter: filter.map(Into::into),
            })),
            _ => unimplemented!("unsupported query {value:?}"),
        }
    }
}

impl From<sqlparser::ast::Query> for SqlQuery {
    fn from(value: sqlparser::ast::Query) -> Self {
        let sqlparser::ast::Query {
            body,
            order_by,
            limit,
            offset,
            ..
        } = value;
        match *body {
            sqlparser::ast::SetExpr::Select(select) => {
                let (tables, join_clauses): (Vec<TableExpr>, Vec<Vec<JoinClause>>) = select
                    .from
                    .into_iter()
                    .map(|table_with_joins| {
                        (
                            table_with_joins.relation.into(),
                            table_with_joins.joins.into_iter().map(Into::into).collect(),
                        )
                    })
                    .unzip();
                let join = join_clauses.into_iter().flatten().collect();
                SqlQuery::Select(SelectStatement {
                    ctes: Vec::new(), // TODO comes from Query.with
                    distinct: matches!(select.distinct, Some(sqlparser::ast::Distinct::Distinct)),
                    fields: select.projection.into_iter().map(Into::into).collect(),
                    tables,
                    join,
                    where_clause: select.selection.map(Into::into),
                    group_by: {
                        let group_by: GroupByClause = select.group_by.into();
                        if group_by.fields.is_empty() {
                            None
                        } else {
                            Some(group_by)
                        }
                    },
                    having: select.having.map(Into::into),
                    order: order_by.map(Into::into),
                    limit_clause: LimitClause::LimitOffset {
                        limit: limit.map(|expr| {
                            if let Expr::Literal(literal) = expr.into() {
                                LimitValue::Literal(literal)
                            } else {
                                unimplemented!("non-literal limit expression");
                            }
                        }),
                        offset: offset.map(|sqlparser::ast::Offset { value: expr, .. }| {
                            if let Expr::Literal(literal) = expr.into() {
                                literal
                            } else {
                                unimplemented!("non-literal offset expression");
                            }
                        }),
                    },
                })
            }
            _ => unimplemented!("{body:?}"),
        }
    }
}

impl From<sqlparser::ast::SelectItem> for FieldDefinitionExpr {
    fn from(value: sqlparser::ast::SelectItem) -> Self {
        use sqlparser::ast::SelectItem::*;
        match value {
            ExprWithAlias { expr, alias } => FieldDefinitionExpr::Expr {
                expr: expr.into(),
                alias: Some(alias.into()),
            },
            UnnamedExpr(expr) => FieldDefinitionExpr::Expr {
                expr: expr.into(),
                alias: None,
            },
            QualifiedWildcard(relation, _options) => {
                FieldDefinitionExpr::AllInTable(relation.into())
            }
            Wildcard(_options) => FieldDefinitionExpr::All,
        }
    }
}

impl From<sqlparser::ast::Ident> for SqlIdentifier {
    fn from(value: sqlparser::ast::Ident) -> Self {
        value.value.into()
    }
}

impl From<sqlparser::ast::ObjectName> for Relation {
    fn from(value: sqlparser::ast::ObjectName) -> Self {
        let mut identifiers = value.0.into_iter().map(Into::into);
        let first = identifiers.next().unwrap_or_default();
        if let Some(second) = identifiers.next() {
            Self {
                name: second,
                schema: Some(first),
            }
        } else {
            Self {
                name: first,
                schema: None,
            }
        }
    }
}

impl From<sqlparser::ast::Expr> for Expr {
    fn from(value: sqlparser::ast::Expr) -> Self {
        use sqlparser::ast::Expr::*;
        match value {
            AllOp {
                left,
                compare_op,
                right,
            } => Self::OpAll {
                lhs: left.into(),
                op: compare_op.into(),
                rhs: right.into(),
            },
            AnyOp {
                left,
                compare_op,
                right,
            } => Self::OpAny {
                lhs: left.into(),
                op: compare_op.into(),
                rhs: right.into(),
            },
            Array(array) => Self::Array(array.elem.into_iter().map(Into::into).collect()),
            AtTimeZone {
                timestamp,
                time_zone,
            } => unimplemented!("{timestamp:?} AT TIMEZONE {time_zone:?}"),
            Between {
                expr,
                negated,
                low,
                high,
            } => Self::Between {
                operand: expr.into(),
                min: low.into(),
                max: high.into(),
                negated,
            },
            BinaryOp { left, op, right } => Self::BinaryOp {
                lhs: left.into(),
                op: op.into(),
                rhs: right.into(),
            },
            Case {
                operand: None, // XXX do we really not support the CASE operand?
                conditions,
                results,
                else_result,
            } => Self::CaseWhen {
                branches: conditions
                    .into_iter()
                    .zip(results)
                    .map(|(condition, result)| CaseWhenBranch {
                        condition: condition.into(),
                        body: result.into(),
                    })
                    .collect(),
                else_expr: else_result.map(Into::into),
            },
            Identifier(ident) => Self::Column(ident.into()),
            Value(value) => Self::Literal(value.into()),
            _ => unimplemented!("{value:?}"),
        }
    }
}

impl From<Box<sqlparser::ast::Expr>> for Box<Expr> {
    fn from(value: Box<sqlparser::ast::Expr>) -> Self {
        Box::new((*value).into())
    }
}

impl From<sqlparser::ast::BinaryOperator> for BinaryOperator {
    fn from(value: sqlparser::ast::BinaryOperator) -> Self {
        use sqlparser::ast::BinaryOperator::*;
        match value {
            And => Self::And,
            Arrow => Self::Arrow1,
            ArrowAt => Self::AtArrowLeft,
            AtArrow => Self::AtArrowRight,
            AtAt => unimplemented!("@@ {value:?}"),
            AtQuestion => unimplemented!("@? {value:?}"),
            BitwiseAnd => unimplemented!("& {value:?}"),
            BitwiseOr => unimplemented!("| {value:?}"),
            BitwiseXor => unimplemented!("^ {value:?}"),
            Custom(_) => unimplemented!("CUSTOM {value:?}"),
            Divide => Self::Divide,
            DuckIntegerDivide => unimplemented!("Duck // {value:?}"),
            Eq => Self::Equal,
            Gt => Self::Greater,
            GtEq => Self::GreaterOrEqual,
            HashArrow => Self::HashArrow1,
            HashLongArrow => Self::HashArrow2,
            HashMinus => Self::HashSubtract,
            LongArrow => Self::Arrow2,
            Lt => Self::Less,
            LtEq => Self::LessOrEqual,
            Modulo => unimplemented!("% {value:?}"),
            Multiply => Self::Multiply,
            MyIntegerDivide => unimplemented!("MySQL DIV {value:?}"),
            NotEq => Self::NotEqual,
            Plus => Self::Add,
            QuestionAnd => Self::QuestionMarkAnd,
            QuestionPipe => Self::QuestionMarkPipe,
            Spaceship => unimplemented!("<=> {value:?}"),

            _ => unimplemented!("PG-specific {value:?}"),
        }
    }
}

impl From<sqlparser::ast::GroupByExpr> for GroupByClause {
    fn from(value: sqlparser::ast::GroupByExpr) -> Self {
        match value {
            sqlparser::ast::GroupByExpr::Expressions(exprs, _modifiers) => GroupByClause {
                fields: exprs.into_iter().map(Into::into).collect(),
            },
            sqlparser::ast::GroupByExpr::All(_) => {
                unimplemented!("Snowflake/DuckDB/ClickHouse group by syntax {value:?}")
            }
        }
    }
}

impl From<sqlparser::ast::Expr> for FieldReference {
    fn from(value: sqlparser::ast::Expr) -> Self {
        if let sqlparser::ast::Expr::Value(sqlparser::ast::Value::Number(ref n, _)) = value {
            if let Ok(i) = n.parse() {
                return FieldReference::Numeric(i);
            }
        }
        FieldReference::Expr(value.into())
    }
}

impl From<sqlparser::ast::OrderBy> for OrderClause {
    fn from(value: sqlparser::ast::OrderBy) -> Self {
        OrderClause {
            order_by: value.exprs.into_iter().map(Into::into).collect(),
        }
    }
}

impl From<sqlparser::ast::OrderByExpr> for OrderBy {
    fn from(value: sqlparser::ast::OrderByExpr) -> Self {
        let sqlparser::ast::OrderByExpr {
            expr,
            asc,
            nulls_first,
            ..
        } = value;
        Self {
            field: expr.into(),
            order_type: asc.map(|asc| {
                if asc {
                    OrderType::OrderAscending
                } else {
                    OrderType::OrderDescending
                }
            }),
            null_order: nulls_first.map(|nulls_first| {
                if nulls_first {
                    NullOrder::NullsFirst
                } else {
                    NullOrder::NullsLast
                }
            }),
        }
    }
}

impl From<sqlparser::ast::TableFactor> for TableExpr {
    fn from(value: sqlparser::ast::TableFactor) -> Self {
        match value {
            sqlparser::ast::TableFactor::Table { name, alias, .. } => Self {
                inner: TableExprInner::Table(name.into()),
                alias: alias.map(|table_alias| table_alias.name.into()), // XXX we don't support [`TableAlias::columns`]
                index_hint: None, // XXX Don't see where this is parsed in sqlparser
            },
            sqlparser::ast::TableFactor::Derived {
                subquery, alias, ..
            } => {
                if let SqlQuery::Select(subselect) = (*subquery).into() {
                    Self {
                        inner: TableExprInner::Subquery(Box::new(subselect)),
                        alias: alias.map(|table_alias| table_alias.name.into()), // XXX we don't support [`TableAlias::columns`]
                        index_hint: None, // XXX Don't see where this is parsed in sqlparser
                    }
                } else {
                    panic!("unexpected non-SELECT subquery in table expression")
                }
            }
            _ => unimplemented!("unsupported table expression {value:?}"),
        }
    }
}

impl From<sqlparser::ast::Join> for JoinClause {
    fn from(value: sqlparser::ast::Join) -> Self {
        Self {
            operator: (&value.join_operator).into(),
            constraint: value.join_operator.into(),
            right: crate::JoinRightSide::Table(value.relation.into()),
        }
    }
}

impl From<&sqlparser::ast::JoinOperator> for JoinOperator {
    fn from(value: &sqlparser::ast::JoinOperator) -> Self {
        use sqlparser::ast::JoinOperator::*;
        match value {
            Inner(..) => Self::InnerJoin,
            LeftOuter(..) => Self::LeftOuterJoin,
            RightOuter(..) => Self::RightJoin, // XXX is this outer?
            CrossJoin => Self::CrossJoin,
            _ => unimplemented!("unsupported join type {value:?}"),
        }
    }
}

impl From<sqlparser::ast::JoinOperator> for JoinConstraint {
    fn from(value: sqlparser::ast::JoinOperator) -> Self {
        use sqlparser::ast::JoinOperator::*;
        match value {
            Inner(constraint) => constraint.into(),
            LeftOuter(constraint) => constraint.into(),
            RightOuter(constraint) => constraint.into(),
            FullOuter(constraint) => constraint.into(),
            CrossJoin => JoinConstraint::Empty,
            LeftSemi(constraint) => constraint.into(),
            RightSemi(constraint) => constraint.into(),
            LeftAnti(constraint) => constraint.into(),
            RightAnti(constraint) => constraint.into(),
            CrossApply => JoinConstraint::Empty,
            OuterApply => JoinConstraint::Empty,
            AsOf { .. } => unimplemented!("unsupported ASOF join"),
        }
    }
}

impl From<sqlparser::ast::JoinConstraint> for JoinConstraint {
    fn from(value: sqlparser::ast::JoinConstraint) -> Self {
        use sqlparser::ast::JoinConstraint::*;
        match value {
            On(expr) => Self::On(expr.into()),
            Using(idents) => Self::Using(idents.into_iter().map(Into::into).collect()),
            None => Self::Empty,
            Natural => unimplemented!("unsupported NATURAL join"),
        }
    }
}

impl From<sqlparser::ast::Ident> for Column {
    fn from(value: sqlparser::ast::Ident) -> Self {
        Self {
            name: value.into(),
            table: None,
        }
    }
}

impl From<String> for ItemPlaceholder {
    fn from(value: String) -> Self {
        if value == "?" {
            Self::QuestionMark
        } else {
            if let Ok((_, placeholder)) = dollarsign_placeholder(LocatedSpan::new(value.as_bytes()))
            {
                placeholder
            } else {
                unimplemented!("nyi placeholder '{value}'")
            }
        }
    }
}

impl From<sqlparser::ast::ShowStatementFilter> for FilterPredicate {
    fn from(value: sqlparser::ast::ShowStatementFilter) -> Self {
        use sqlparser::ast::ShowStatementFilter::*;
        match value {
            Like(like) => Self::Like(like),
            Where(expr) => Self::Where(expr.into()),
            ILike(_) => unimplemented!("not supported for MySQL or Postgres"),
        }
    }
}

impl From<sqlparser::ast::Value> for Literal {
    fn from(value: sqlparser::ast::Value) -> Self {
        use sqlparser::ast::Value::*;
        match value {
            Placeholder(name) => Literal::Placeholder(name.into()),
            Boolean(b) => Literal::Boolean(b),
            Null => Literal::Null,
            DoubleQuotedString(s)
            | SingleQuotedString(s)
            | DoubleQuotedByteStringLiteral(s)
            | SingleQuotedByteStringLiteral(s) => Literal::String(s),
            DollarQuotedString(sqlparser::ast::DollarQuotedString { value, .. }) => {
                Literal::String(value)
            }
            Number(s, _unknown) => Literal::Integer(s.parse().expect("TODO fix number parsing")),
            _ => unimplemented!("unsupported literal {value:?}"),
        }
    }
}

/// First, attempt to parse certain readyset extensions; then, parse using sqlparser-rs. The common case is presumably
/// "everything except readyset", so this should be reversed.
pub fn sql_query_sqlparser(
    dialect: Dialect,
) -> impl Fn(LocatedSpan<&[u8]>) -> NomSqlResult<&[u8], SqlQuery> {
    move |i| {
        if let Ok((i, q)) = alt((
            map(drop_cached_query(dialect), SqlQuery::DropCache),
            map(drop_all_caches, SqlQuery::DropAllCaches),
            map(drop_all_proxied_queries(), SqlQuery::DropAllProxiedQueries),
            map(explain_statement(dialect), SqlQuery::Explain),
            map(create_cached_query(dialect), SqlQuery::CreateCache),
        ))(i)
        {
            Ok((i, q))
        } else {
            let sqlparser_dialect: &dyn sqlparser::dialect::Dialect = match dialect {
                Dialect::MySQL => &sqlparser::dialect::MySqlDialect {},
                Dialect::PostgreSQL => &sqlparser::dialect::PostgreSqlDialect {},
            };
            // TODO: add any modicum of actual error handling
            let mut parser = sqlparser::parser::Parser::new(sqlparser_dialect)
                .try_with_sql(
                    str::from_utf8(i.as_bytes())
                        .inspect(|f| {
                            dbg!(f);
                        })
                        .map_err(|_| {
                            nom::Err::Error(NomSqlError {
                                input: i,
                                kind: ErrorKind::Fail,
                            })
                        })?,
                )
                .map_err(|_| {
                    nom::Err::Error(NomSqlError {
                        input: i,
                        kind: ErrorKind::Fail,
                    })
                })?;
            let statement = parser.parse_statement().map_err(|_| {
                nom::Err::Error(NomSqlError {
                    input: i,
                    kind: ErrorKind::Fail,
                })
            })?;
            Ok((i, dbg!(statement.into())))
        }
    }
}
