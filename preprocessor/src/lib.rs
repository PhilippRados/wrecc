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
    filename: String,
}

impl<'a> Preprocessor<'a> {
    pub fn new(filename: &'a str, input: &'a str) -> Self {
        Preprocessor {
            source: input.chars().peekable(),
            raw_source: input
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
            line: 1,
            column: 1,
            filename: filename.to_string(),
        }
    }

    fn consume_until(&mut self, expected: Vec<char>) -> String {
        let mut consumed = String::new();

        while let Some(v) = self.source.by_ref().next_if(|c| !expected.contains(c)) {
            consumed.push(v);
        }

        consumed
    }

    fn consume_while(&mut self, expected: Vec<char>) -> String {
        let mut consumed = String::new();

        while let Some(v) = self.source.by_ref().next_if(|c| expected.contains(c)) {
            consumed.push(v);
        }

        consumed
    }
    fn root_path() -> String {
        use std::env;
        env::var("CARGO_MANIFEST_DIR").unwrap()
    }
    fn paste_header(&self, file_path: &str) -> Result<String, Error> {
        let root = Self::root_path();
        let abs_path = root + "/include/" + file_path;

        let data = fs::read_to_string(&abs_path).or(Err(Error::new(
            self,
            ErrorKind::InvalidHeader(file_path.to_string()),
        )))?;

        let header_prologue = format!("#pro:{}\n", file_path);
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }
    pub fn preprocess(mut self) -> Result<String, Vec<Error>> {
        let mut result = String::from("");
        let mut errors = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '#' => match self.consume_until(vec![' ']).as_ref() {
                    "include" => {
                        self.consume_while(vec![' ', '\t']);

                        match self.source.next() {
                            Some('<') => {
                                let file = self.consume_until(vec!['>', '\n']);
                                self.source.next();

                                match self.paste_header(&file) {
                                    Ok(header_data) => result.push_str(&header_data),
                                    Err(e) => {
                                        errors.push(e);
                                        continue;
                                    }
                                }
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
    fn filename(&self) -> String {
        self.filename.to_string()
    }
}
