pub fn pretty_integer(i: usize) -> String {
    // ex: 123456789 -> "123,456,789"
    let s = i.to_string();
    let chars: Vec<char> = s.chars().collect();
    let mut result = String::new();

    for (index, ch) in chars.iter().enumerate() {
        if index > 0 && (chars.len() - index) % 3 == 0 {
            result.push(',');
        }
        result.push(*ch);
    }

    result
}
