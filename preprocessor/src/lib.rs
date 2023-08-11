// pub mod preprocessor;

use compiler::Error;
use compiler::ErrorKind;
use compiler::Location;
use std::fs;
use std::iter::Peekable;
use std::str::Chars;

pub struct Preprocessor<'a> {
    source: Peekable<Chars<'a>>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
}

impl<'a> Preprocessor<'a> {
    pub fn new(input: &'a str) -> Self {
        Preprocessor {
            source: input.chars().peekable(),
            raw_source: input
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
            line: 1,
            column: 1,
        }
    }

    fn consume_until(&mut self, expected: char) -> String {
        let mut directive = String::new();

        while let Some(v) = self.source.by_ref().next_if(|c| *c != expected) {
            directive.push(v);
        }

        directive
    }
    fn paste_header(&self, file_path: &str) -> Result<String, Error> {
        let data = fs::read_to_string(file_path).expect("check read-to-string fail reasons");
        let header_metadata = format!("# {}", self.line);

        Ok(data + &header_metadata)
    }
    fn consume(&mut self, expected: char, msg: &'static str) -> Result<(), Error> {
        match self.source.next() {
            Some(c) if c == expected => Ok(()),
            _ => Err(Error::new(self, ErrorKind::Regular(msg))),
        }
    }
    fn get_header_path(&mut self) -> String {
        // let header = self.consume_until('>');
        let mut header = String::new();

        while let Some(v) = self.source.by_ref().next_if(|c| c.is_alphabetic()) {
            header.push(v);
        }

        header
    }
    pub fn preprocess(mut self) -> Result<String, Vec<Error>> {
        let mut result = String::from("");
        let mut errors = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '#' => match self.consume_until(' ').as_ref() {
                    "include" => {
                        while self
                            .source
                            .by_ref()
                            .next_if(|c| *c == ' ' || *c == '\t')
                            .is_some()
                        {}

                        match self.source.next() {
                            Some('<') => {
                                let file = self.get_header_path();
                                self.consume('>', "Expect closing '>' after include-directive");
                                // .or_else(|e| errors.push(e));

                                result.push_str(&self.paste_header(&file).unwrap());
                                //.or_else(|e| errors.push(e));
                            }
                            Some('"') => todo!(),
                            _ => errors.push(Error::new(
                                &self,
                                ErrorKind::Regular(
                                    "Expected opening '<' or '\"' after include directive",
                                ),
                            )),
                        }
                    }
                    d => errors.push(Error::new(
                        &self,
                        ErrorKind::InvalidDirective(d.to_string()),
                    )),
                },
                '/' => {
                    // if self.matches('/') {
                    //     // there has to be a better way to consume the iter without the first \n
                    //     while self
                    //         .source
                    //         .by_ref()
                    //         .next_if(|&c| c != '\n' && c != '\0')
                    //         .is_some()
                    //     {}
                    // } else if self.matches('*') {
                    //     // parse multiline comment
                    //     self.column += 2;
                    //     while let Some(c) = self.source.next() {
                    //         match c {
                    //             '\n' => {
                    //                 self.line += 1;
                    //                 self.column = 1
                    //             }
                    //             '*' if self.matches('/') => {
                    //                 self.column += 2;
                    //                 break;
                    //             }
                    //             _ => self.column += 1,
                    //         }
                    //     }
                    // }
                    result.push(c);
                }
                '\n' => {
                    self.line += 1;
                    result.push(c);
                }
                _ => result.push(c),
            }
        }

        if errors.is_empty() {
            Ok(result)
        } else {
            Err(errors)
        }
    }
}
impl<'a> Location for Preprocessor<'a> {
    fn line_index(&self) -> i32 {
        self.line
    }
    fn column(&self) -> i32 {
        self.column
    }
    fn line_string(&self) -> String {
        self.raw_source[(self.line - 1) as usize].clone()
    }
}
