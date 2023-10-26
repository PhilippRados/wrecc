use crate::compiler::common::{expr::*, token::*, types::*};
use crate::compiler::wrecc_parser::parser::*;

// int a[3] = {1,2,3};
// equivalent to:
// int a[3];
// a[0] = 1;
// a[1] = 2;
// a[2] = 3;
pub fn init_list_sugar(token: Token, type_decl: &NEWTypes, list: Vec<Expr>) -> Vec<Expr> {
    let mut result = Vec::new();
    for (i, expr) in list
        .into_iter()
        .enumerate()
        .filter(|(_, expr)| !matches!(expr.kind, ExprKind::Nop))
    {
        let l_expr = access_sugar(
            &token,
            type_decl,
            i,
            Expr::new(ExprKind::Ident(token.clone()), ValueKind::Lvalue),
        );

        result.push(Expr::new(
            ExprKind::Assign {
                l_expr: Box::new(l_expr),
                token: token.clone(),
                r_expr: Box::new(expr),
            },
            ValueKind::Rvalue,
        ))
    }
    result
}

// recursively generates the syntax sugar to index an array or struct/union
// given this type: int a[2][3] and index 4
// it generates the nested accesses to get to the element at index 3
// => a[1][1]
fn access_sugar(name: &Token, type_decl: &NEWTypes, i: usize, left: Expr) -> Expr {
    match type_decl {
        NEWTypes::Array { amount, of } => {
            let divisor = type_element_count(type_decl) / amount;
            let current_i = i / divisor;
            let new_i = i % divisor;

            let current_i = Expr::new_literal(current_i as i64, Types::Int);

            access_sugar(name, of, new_i, index_sugar(name.clone(), left, current_i))
        }
        NEWTypes::Struct(s) | NEWTypes::Union(s) => {
            let members = s.members();
            let (member_index, new_i) = get_member_index(&members, i);
            let (member_type, member) = members[member_index].clone();

            access_sugar(
                name,
                &member_type,
                new_i,
                Expr::new(
                    ExprKind::MemberAccess {
                        member,
                        token: name.clone(),
                        expr: Box::new(left),
                    },
                    ValueKind::Lvalue,
                ),
            )
        }
        _ => left,
    }
}
fn get_member_index(members: &Vec<(NEWTypes, Token)>, i: usize) -> (usize, usize) {
    let mut acc = 0;
    let mut index = 0;

    for (ty, _) in members {
        if (acc + type_element_count(ty)) <= i {
            acc += type_element_count(ty);
            index += 1;
        } else {
            break;
        }
    }

    let new_index = i - acc;
    (index, new_index)
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
        #[test]
        fn complex_struct() {
            let point = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
            ]));
            let line = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (point.clone(), Token::default(TokenType::Comma)),
                (point.clone(), Token::default(TokenType::Comma)),
            ]));
            let person = NEWTypes::Struct(StructInfo::Anonymous(vec![
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
                (line.clone(), Token::default(TokenType::Comma)),
            ]));

            let expected = ElementType::Multiple(vec![
                ElementType::Multiple(vec![
                    ElementType::Single(person.clone()),
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
                    ElementType::Single(line.clone()),
                    ElementType::Single(point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ElementType::Multiple(vec![
                    ElementType::Single(point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
            ]);
            let actual = init_default(&person);

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
