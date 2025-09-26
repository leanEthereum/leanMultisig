/// Preprocesses source code by removing comments and normalizing whitespace.
pub fn preprocess_source(input: &str) -> String {
    input
        .lines()
        .map(|line| {
            // Remove line comments (everything after //)
            if let Some(pos) = line.find("//") {
                line[..pos].trim_end()
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comment_removal() {
        let input = r#"
            let x = 5; // This is a comment
            let y = 10;
            // This whole line is a comment
            let z = x + y;
        "#;

        let expected = r#"
            let x = 5;
            let y = 10;

            let z = x + y;
        "#;

        assert_eq!(preprocess_source(input), expected);
    }

    #[test]
    fn test_no_comments() {
        let input = "let x = 5;\nlet y = 10;";
        assert_eq!(preprocess_source(input), input);
    }

    #[test]
    fn test_empty_lines_preserved() {
        let input = "line1\n\nline3";
        assert_eq!(preprocess_source(input), input);
    }
}
