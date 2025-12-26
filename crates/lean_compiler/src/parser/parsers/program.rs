use super::function::FunctionParser;
use super::literal::ConstantDeclarationParser;
use crate::{
    CompilationFlags, ProgramSource,
    lang::{Program, SourceLocation},
    parser::{
        error::{ParseError, ParseResult, SemanticError},
        grammar::{ParsePair, Rule, parse_source},
        lexer,
        parsers::{Parse, ParseContext, ParsedConstant, next_inner_pair},
    },
};
use std::collections::BTreeMap;
use std::path::Path;

/// Parser for complete programs.
pub struct ProgramParser;

impl Parse<Program> for ProgramParser {
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<Program> {
        let mut functions = BTreeMap::new();
        let mut function_locations = BTreeMap::new();
        let mut source_code = BTreeMap::new();
        let mut filepaths = BTreeMap::new();
        let file_id = ctx.get_next_file_id();
        ctx.current_file_id = file_id;
        filepaths.insert(file_id, ctx.current_filepath.clone());
        source_code.insert(file_id, ctx.current_source_code.clone());

        for item in pair.into_inner() {
            match item.as_rule() {
                Rule::constant_declaration => {
                    let (name, value) = ConstantDeclarationParser.parse(item, ctx)?;
                    match value {
                        ParsedConstant::Scalar(v) => ctx.add_constant(name, v)?,
                        ParsedConstant::Array(arr) => ctx.add_const_array(name, arr)?,
                    }
                }
                Rule::import_statement => {
                    // Visit the imported file and parse it into the context
                    // and program; also keep track of which files have been
                    // imported and do not import the same file twice.
                    let filepath = ImportStatementParser.parse(item, ctx)?;
                    let filepath = Path::new(&ctx.current_filepath)
                        .parent()
                        .expect("Empty filepath")
                        .join(filepath)
                        .to_str()
                        .expect("Invalid UTF-8 in filepath")
                        .to_string();
                    if !ctx.imported_filepaths.contains(&filepath) {
                        let saved_filepath = ctx.current_filepath.clone();
                        let saved_file_id = ctx.current_file_id;
                        ctx.current_filepath = filepath.clone();
                        ctx.imported_filepaths.insert(filepath.clone());
                        ctx.current_source_code = ProgramSource::Filepath(filepath.clone())
                            .get_content(&ctx.flags)
                            .unwrap();
                        let subprogram = parse_program_helper(ctx)?;
                        functions.extend(subprogram.functions);
                        function_locations.extend(subprogram.function_locations);
                        source_code.extend(subprogram.source_code);
                        filepaths.extend(subprogram.filepaths);
                        ctx.current_filepath = saved_filepath;
                        ctx.current_file_id = saved_file_id;
                        // It is unnecessary to save and restore current_source_code because it will not
                        // be referenced again for the same file.
                    }
                }
                Rule::function => {
                    let line_number = item.line_col().0;
                    let location = SourceLocation { file_id, line_number };
                    let function = FunctionParser.parse(item, ctx)?;
                    let name = function.name.clone();

                    function_locations.insert(location, name.clone());

                    if functions.insert(name.clone(), function).is_some() {
                        return Err(SemanticError::with_context(
                            format!("Multiply defined function: {name}"),
                            "function definition",
                        )
                        .into());
                    }
                }
                Rule::EOI => break,
                _ => {} // Skip other rules
            }
        }

        Ok(Program {
            functions,
            const_arrays: ctx.const_arrays.clone(),
            function_locations,
            filepaths,
            source_code,
        })
    }
}

/// Parser for import statements.
pub struct ImportStatementParser;

impl Parse<String> for ImportStatementParser {
    fn parse(&self, pair: ParsePair<'_>, _ctx: &mut ParseContext) -> ParseResult<String> {
        let mut inner = pair.into_inner();
        let item = next_inner_pair(&mut inner, "filepath")?;
        match item.as_rule() {
            Rule::filepath => {
                let inner = item.into_inner();
                let mut filepath = String::new();
                for item in inner {
                    match item.as_rule() {
                        Rule::filepath_character => {
                            filepath.push_str(item.as_str());
                        }
                        _ => {
                            return Err(SemanticError::with_context(
                                format!("Expected a filepath character, got: {}", item.as_str()),
                                "filepath character",
                            )
                            .into());
                        }
                    }
                }
                Ok(filepath)
            }
            _ => Err(
                SemanticError::with_context(format!("Expected a filepath, got: {}", item.as_str()), "filepath").into(),
            ),
        }
    }
}

fn parse_program_helper(ctx: &mut ParseContext) -> Result<Program, ParseError> {
    // Preprocess source to remove comments
    let processed_input = lexer::preprocess_source(&ctx.current_source_code);

    // Parse grammar into AST nodes
    let program_pair = parse_source(&processed_input)?;

    // Parse into semantic structures
    ProgramParser.parse(program_pair, ctx)
}

pub fn parse_program(input: &ProgramSource, flags: CompilationFlags) -> Result<Program, ParseError> {
    parse_program_helper(&mut ParseContext::new(input, flags)?)
}
