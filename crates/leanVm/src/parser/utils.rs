pub(crate) fn remove_comments(input: &str) -> String {
    input
        .lines()
        .map(|line| line.find("//").map_or(line, |pos| &line[..pos]))
        .collect::<Vec<_>>()
        .join("\n")
}
