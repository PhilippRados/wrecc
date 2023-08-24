use compiler::consume_while;
use compiler::Error;
use compiler::ErrorKind;
use compiler::Location;

use std::collections::HashMap;
use std::fs;
use std::iter::Peekable;
use std::str::Chars;

pub struct Preprocessor<'a> {
    source: Peekable<Chars<'a>>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
    filename: String,
    defines: HashMap<String, String>,
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
            defines: HashMap::new(),
        }
    }

    fn paste_header(&mut self, file_path: &str) -> Result<String, Vec<Error>> {
        // WARN: only temporary absolute path. /include will be found via PATH env var
        let abs_path =
            "/Users/philipprados/documents/coding/Rust/rucc/include/".to_string() + file_path;

        let data = fs::read_to_string(&abs_path).or(Err(vec![Error::new(
            self,
            ErrorKind::InvalidHeader(file_path.to_string()),
        )]))?;

        let (data, defines) = Preprocessor::new(&file_path, &data).preprocess()?;

        // TODO: check what happens if two hashmaps have same key
        // if there were #defines defined in the included file, include them in current file too
        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path);
        // TODO: maybe can use same marker token \n
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn consume_comment(&mut self) -> String {
        let mut result = String::new();

        match self.source.next() {
            Some(c @ '/') => {
                result.push(c);
                result.push_str(&consume_while(
                    &mut self.source,
                    |c| c != '\n' && c != '\0',
                    false,
                ));
            }
            Some(c @ '*') => {
                result.push(c);
                while let Some(c) = self.source.next() {
                    result.push(c);
                    match c {
                        '\n' => {
                            self.line += 1;
                        }
                        '*' => match self.source.next() {
                            Some(c @ '/') => {
                                result.push(c);
                                self.column += 2;
                                break;
                            }
                            Some(c) => result.push(c),
                            None => (),
                        },
                        _ => self.column += 1,
                    }
                }
            }
            Some(c) => result.push(c),
            None => (),
        }
        result
    }
    fn include(&mut self) -> Result<String, Vec<Error>> {
        match self.source.next() {
            Some('<') => {
                let file = consume_while(&mut self.source, |c| c != '>' && c != '\n', false);

                if let Some('\n') = self.source.next() {
                    return Err(vec![Error::new(
                        self,
                        ErrorKind::Regular("Expected closing '>' after header file"),
                    )]);
                }

                self.paste_header(&file)
            }
            Some('"') => todo!(),
            _ => Err(vec![Error::new(
                self,
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            )]),
        }
    }
    fn define(&mut self) -> Result<(), Error> {
        let identifier = consume_while(&mut self.source, |c| c != ' ' && c != '\t', false);
        consume_while(&mut self.source, |c| c == ' ' && c == '\t', true);

        let replace_with = consume_while(&mut self.source, |c| c != '\n', false);

        self.defines.insert(identifier, replace_with);

        Ok(())
    }
    pub fn preprocess(mut self) -> Result<(String, HashMap<String, String>), Vec<Error>> {
        let mut result = String::from("");
        let mut errors = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '#' if is_first_line_token(&result) => {
                    match consume_while(
                        &mut self.source,
                        |c| c != ' ' && c != '\t' && c != '\n',
                        false,
                    )
                    .as_ref()
                    {
                        "include" => {
                            consume_while(&mut self.source, |c| c == ' ' || c == '\t', false);

                            result.push_str(&self.include()?)
                        }
                        "define" => {
                            consume_while(&mut self.source, |c| c == ' ' || c == '\t', false);

                            if let Err(e) = self.define() {
                                errors.push(e)
                            }
                        }
                        directive => errors.push(Error::new(
                            &self,
                            ErrorKind::InvalidDirective(directive.to_string()),
                        )),
                    }
                }

                // have to consume comments/string/chars seperately so that # directives aren't processed
                '/' => {
                    result.push(c);
                    result.push_str(&self.consume_comment());
                }
                '"' | '\'' => {
                    result.push(c);
                    result.push_str(&consume_while(&mut self.source, |ch| ch != c, false));
                    if let Some(c) = self.source.next() {
                        result.push(c)
                    }
                }
                '\n' => {
                    self.line += 1;
                    result.push(c);
                }
                _ if c.is_alphabetic() => {
                    let ident = c.to_string()
                        + &consume_while(
                            &mut self.source,
                            |c| c.is_alphabetic() || c == '_' || c.is_ascii_digit(),
                            false,
                        );

                    if let Some(replacement) = self.defines.get(&ident) {
                        result.push_str(replacement)
                    } else {
                        result.push_str(&ident)
                    }
                }
                _ => result.push(c),
            }
        }

        if errors.is_empty() {
            Ok((result, self.defines))
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

fn is_first_line_token(prev_tokens: &str) -> bool {
    for c in prev_tokens.chars().rev() {
        match c {
            '\n' => return true,
            ' ' | '\t' => (),
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    #[test]
    fn parses_header_file() {
        let mut input = "here.h>\nint some;".chars().peekable();
        let actual = consume_while(&mut input, |c| c != '>' && c != '\n', false);

        let expected = "here.h";
        let expected_steam = ">\nint some;";

        assert_eq!(actual, expected);
        assert_eq!(input.collect::<String>(), expected_steam);
    }

    #[test]
    fn first_line_token() {
        assert_eq!(is_first_line_token(""), true);
        assert_eq!(is_first_line_token("\n  \t "), true);
        assert_eq!(is_first_line_token("\nint\n "), true);
        assert_eq!(is_first_line_token("\nint "), false);
        assert_eq!(is_first_line_token("+ "), false);
    }
}
