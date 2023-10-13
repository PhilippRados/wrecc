use crate::common::{expr::*, token::*, types::*};
use crate::parser::parser::*;

pub fn init_list_sugar(
    token: Token,
    list: &mut Vec<Expr>,
    type_decl: NEWTypes,
    is_outer: bool,
    left: Expr,
) -> Vec<Expr> {
    // int a[3] = {1,2,3};
    // equivalent to:
    // int a[3];
    // a[0] = 1;
    // a[1] = 2;
    // a[2] = 3;
    if let NEWTypes::Array { amount, of } = type_decl.clone() {
        let mut result = Vec::new();
        for ((i, _), arr_i) in list
            .iter()
            .enumerate()
            .step_by(type_element_count(&of))
            .zip(0..amount)
        {
            for (offset, l_expr) in init_list_sugar(
                token.clone(),
                &mut list[i..list.len()].to_vec(),
                *of.clone(),
                false,
                index_sugar(
                    token.clone(),
                    left.clone(),
                    Expr::new_literal(arr_i as i64, Types::Int),
                ),
            )
            .into_iter()
            .enumerate()
            {
                let value = replace_default(&list[i + offset]);
                result.push(match is_outer {
                    true => Expr::new(
                        ExprKind::Assign {
                            l_expr: Box::new(l_expr),
                            token: token.clone(),
                            r_expr: Box::new(value),
                        },
                        ValueKind::Rvalue,
                    ),
                    false => l_expr,
                })
            }
        }
        result
    } else if let NEWTypes::Struct(s) | NEWTypes::Union(s) = type_decl.clone() {
        let mut result = Vec::new();
        let mut members = s.members().to_vec();

        if let NEWTypes::Union(_) = type_decl {
            remove_unused_members(&mut members, list);
        }

        for member_i in 0..members.len() {
            let i = members
                .iter()
                .take(member_i)
                .fold(0, |acc, (t, _)| acc + type_element_count(t));
            for (offset, l_expr) in init_list_sugar(
                token.clone(),
                &mut list[i..list.len()].to_vec(),
                members[member_i].clone().0,
                false,
                Expr::new(
                    ExprKind::MemberAccess {
                        token: token.clone(),
                        member: members[member_i].clone().1,
                        expr: Box::new(left.clone()),
                    },
                    ValueKind::Lvalue,
                ),
            )
            .into_iter()
            .enumerate()
            {
                let value = replace_default(&list[i + offset]);
                result.push(match is_outer {
                    true => Expr::new(
                        ExprKind::Assign {
                            l_expr: Box::new(l_expr),
                            token: token.clone(),
                            r_expr: Box::new(value),
                        },
                        ValueKind::Rvalue,
                    ),
                    false => l_expr,
                })
            }
        }
        result
    } else {
        vec![left]
    }
}
// returns the length of the flattened type
pub fn type_element_count(type_decl: &NEWTypes) -> usize {
    match type_decl {
        NEWTypes::Array { amount, of } => amount * type_element_count(of),
        NEWTypes::Struct(s) | NEWTypes::Union(s) => {
            let mut result = 0;
            for m in s.members().iter() {
                result += type_element_count(&m.0);
            }
            result
        }
        _ => 1,
    }
}

// creates the flattened list with all the aggregate types broken down in its primitives default types
pub fn fill_default(type_decl: &NEWTypes) -> Vec<Expr> {
    match type_decl {
        NEWTypes::Primitive(_) | NEWTypes::Enum(..) => vec![Expr {
            kind: ExprKind::Nop,
            value_kind: ValueKind::Rvalue,
            type_decl: Some(NEWTypes::default()),
        }],
        NEWTypes::Array { amount, of } => {
            let mut result = Vec::with_capacity(*amount);
            for _ in 0..*amount {
                result.append(&mut fill_default(of))
            }
            result
        }
        NEWTypes::Pointer(_) => vec![Expr {
            kind: ExprKind::Nop,
            value_kind: ValueKind::Rvalue,
            type_decl: Some(NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                Types::Void,
            )))),
        }],
        NEWTypes::Struct(s) | NEWTypes::Union(s) => {
            let mut result = Vec::new();
            for (member_type, _) in s.members().iter() {
                result.append(&mut fill_default(member_type))
            }
            result
        }
    }
}

fn replace_default(expr: &Expr) -> Expr {
    if let ExprKind::Nop = expr.kind {
        Expr {
            kind: ExprKind::Literal(0),
            value_kind: ValueKind::Rvalue,
            type_decl: expr.type_decl.clone(), // is filled in by fill_default()
        }
    } else {
        expr.clone()
    }
}

fn remove_unused_members(members: &mut Vec<(NEWTypes, Token)>, list: &mut Vec<Expr>) {
    // remove unused members so they don't overwrite existing ones
    let old_members = members.clone();
    let mut new_members = vec![];
    let mut new_list = vec![];
    let mut i = 0;

    for m in old_members.iter() {
        let type_len = type_element_count(&m.0);
        if !list[i..i + type_len]
            .iter()
            .all(|e| matches!(e.kind, ExprKind::Nop))
        {
            new_members.push(m.clone());
            for e in list[i..i + type_len].iter() {
                new_list.push(e.clone())
            }
        }
        i += type_len;
    }

    *list = new_list;
    *members = new_members;
}

// TODO: this definitely needs a cleanup/rewrite
// creates a list of types for any given initializer list
// since at any index the type can be the aggregate type or the first primitive type of the aggregate
pub mod init_list_types {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum ElementType {
        Multiple(Vec<ElementType>),
        Single(NEWTypes),
    }
    impl ElementType {
        pub fn contains_char_arr(&self) -> Option<NEWTypes> {
            match self {
                Self::Multiple(m) => m.iter().find_map(|x| x.contains_char_arr()),
                Self::Single(t) => match t {
                    NEWTypes::Array { of, .. }
                        if matches!(**of, NEWTypes::Primitive(Types::Char)) =>
                    {
                        Some(t.clone())
                    }
                    _ => None,
                },
            }
        }
        pub fn at(&self, depth: usize) -> NEWTypes {
            match self {
                Self::Multiple(m) => {
                    if let ElementType::Single(s) = m[depth].clone() {
                        s
                    } else {
                        unreachable!()
                    }
                }
                Self::Single(t) => t.clone(),
            }
        }
        pub fn flatten(&self) -> Vec<ElementType> {
            match self {
                Self::Multiple(v) => {
                    let mut result = vec![];
                    for e in v {
                        if let ElementType::Multiple(..) = *e {
                            for s in e.flatten() {
                                result.push(s);
                            }
                        } else {
                            result.push(e.clone());
                        }
                    }
                    result
                }
                Self::Single(_) => vec![self.clone()],
            }
        }
    }

    // creates array that groups types when they are at the same index:
    // struct Some {
    //   char s[3];
    //   int age;
    // };
    // struct Some arr[2];
    // => [Multiple(Some-arr,Some,Char-arr,Char),Single(Char),Single(Char),Single(Int),
    // Multiple(Some-arr,Some,Char-arr,Char),Single(Char),Single(Char),Single(Int)]
    pub fn init_default(type_decl: &NEWTypes) -> ElementType {
        match type_decl {
            NEWTypes::Array { of, amount } => match init_default(of) {
                ElementType::Single(s) => {
                    let start = ElementType::Multiple(vec![
                        ElementType::Single(type_decl.clone()),
                        ElementType::Single(s.clone()),
                    ]);
                    let mut result = vec![start];
                    for _ in 1..*amount {
                        result.push(ElementType::Single(s.clone()));
                    }
                    ElementType::Multiple(result)
                }
                ElementType::Multiple(v) => {
                    let mut start = vec![ElementType::Single(type_decl.clone())];
                    let mut rest_start = vec![];
                    for e in v[0].flatten() {
                        start.push(e.clone());
                        rest_start.push(e);
                    }
                    let mut result = vec![ElementType::Multiple(start)];
                    let mut rest = vec![ElementType::Multiple(rest_start)];

                    for e in v.into_iter().skip(1) {
                        result.push(e.clone());
                        rest.push(e);
                    }
                    for _ in 1..*amount {
                        for e in rest.clone() {
                            result.push(e);
                        }
                    }
                    ElementType::Multiple(result)
                }
            },
            NEWTypes::Struct(s) | NEWTypes::Union(s) => {
                let mut start = vec![ElementType::Single(type_decl.clone())];
                let mut result = vec![];
                for (i, (t, _)) in s.members().iter().enumerate() {
                    match init_default(t) {
                        ElementType::Single(s) => {
                            if i == 0 {
                                start.push(ElementType::Single(s))
                            } else {
                                result.push(ElementType::Single(s))
                            }
                        }
                        ElementType::Multiple(v) => {
                            if i == 0 {
                                for e in v[0].flatten() {
                                    start.push(e);
                                }
                                for e in v.clone().into_iter().skip(1) {
                                    result.push(e);
                                }
                            } else {
                                for e in v.clone().into_iter() {
                                    result.push(e);
                                }
                            }
                        }
                    };
                }
                result.insert(0, ElementType::Multiple(start));
                ElementType::Multiple(result)
            }
            _ => ElementType::Single(type_decl.clone()),
        }
    }
    #[cfg(test)]
    mod tests {
        use super::*;

        // typedef struct {
        //   int x;
        //   int y;
        // } Point;

        // typedef struct {
        //   Point start;
        //   Point end;
        // } Line;

        // typedef struct {
        //   char name[5];
        //   int age;
        //   Line address;
        // } Person;
        #[allow(non_snake_case)]
        #[test]
        fn complex_struct() {
            let Point = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
            ]));
            let Line = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (Point.clone(), Token::default(TokenType::Comma)),
                (Point.clone(), Token::default(TokenType::Comma)),
            ]));
            let Person = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (
                    NEWTypes::Array {
                        of: Box::new(NEWTypes::Primitive(Types::Char)),
                        amount: 5,
                    },
                    Token::default(TokenType::Comma),
                ),
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
                (Line.clone(), Token::default(TokenType::Comma)),
            ]));

            let expected = ElementType::Multiple(vec![
                ElementType::Multiple(vec![
                    ElementType::Single(Person.clone()),
                    ElementType::Single(NEWTypes::Array {
                        of: Box::new(NEWTypes::Primitive(Types::Char)),
                        amount: 5,
                    }),
                    ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ElementType::Multiple(vec![
                    ElementType::Single(Line.clone()),
                    ElementType::Single(Point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ElementType::Multiple(vec![
                    ElementType::Single(Point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
            ]);
            let actual = init_default(&Person);

            assert_eq!(actual, expected);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multidimensional_array_size() {
        let input = NEWTypes::Array {
            amount: 2,
            of: Box::new(NEWTypes::Array {
                amount: 2,
                of: Box::new(NEWTypes::Primitive(Types::Int)),
            }),
        };
        let actual = type_element_count(&input);

        assert_eq!(actual, 4);
    }
}
