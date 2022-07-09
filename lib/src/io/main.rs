use oxigraph::io::{GraphFormat, GraphParser};
use std::io::Cursor;


fn main() {
    let file = "<http://example.com/s> <http://example.com/p> <http://example.com/o> .";

    let parser = GraphParser::from_format(GraphFormat::NTriples);
    let triples = parser.read_triples(Cursor::new(file))?.collect::<Result<Vec<_>,_>>()?;
    
    assert_eq!(triples.len(), 1);
    assert_eq!(triples[0].subject.to_string(), "<http://example.com/s>");
}
