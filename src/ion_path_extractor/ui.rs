use crate::ion_path_extractor::PathErr;
use crate::{
    Annotations, Element, ElementReader, IonError, IonType, ReaderBuilder, Symbol, UserReader,
    Value,
};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Pointer};
use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
pub enum PathError {
    #[error("Bad path step {0}")]
    BadStep(String),

    #[error("Error parsing path: [{0}]")]
    PathParse(IonError),
}

impl From<IonError> for PathError {
    fn from(e: IonError) -> Self {
        PathError::PathParse(e)
    }
}

#[derive(Debug, Clone)]
enum StringMatch {
    Sensitive(String),
    Insensitive(String),
}

impl Display for StringMatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StringMatch::Sensitive(s) => std::fmt::Display::fmt(&s, f),
            StringMatch::Insensitive(s) => std::fmt::Display::fmt(&s, f),
        }
    }
}

#[derive(Debug, Clone)]
enum Step {
    Index(usize),
    WildCard(),
    Field(StringMatch),
}

impl Display for Step {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Step::Index(i) => std::fmt::Display::fmt(&i, f),
            Step::WildCard() => {
                write!(f, "*")
            }
            Step::Field(field) => std::fmt::Display::fmt(&field, f),
        }
    }
}

type AnnotationMatch = Vec<StringMatch>;

#[derive(Debug, Clone)]
struct PathStep(AnnotationMatch, Step);

impl Display for PathStep {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let PathStep(annot, step) = self;
        for ann in annot {
            std::fmt::Display::fmt(&ann, f)?;
            write!(f, "::")?;
        }
        std::fmt::Display::fmt(&step, f)
    }
}

#[derive(Debug, Clone)]
struct PathSteps(pub Vec<PathStep>);

impl FromIterator<PathStep> for PathSteps {
    fn from_iter<T: IntoIterator<Item = PathStep>>(iter: T) -> Self {
        PathSteps(iter.into_iter().collect())
    }
}

impl Display for PathSteps {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let PathSteps(steps) = self;
        write!(f, "(")?;
        let mut first = true;
        for step in steps {
            if !first {
                write!(f, " ")?;
            }
            std::fmt::Display::fmt(&step, f)?;
            first = false;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, Default)]
struct PathParser {}

impl PathParser {
    fn parse_path(&self, path: &str) -> Result<PathSteps, PathError> {
        let mut reader = ReaderBuilder::new().build(path)?;
        let path = reader.read_one_element()?;
        let path = path.expect_sequence()?;
        path.iter().map(|step| self.parse_path_step(step)).collect()
    }

    fn parse_path_step(&self, step: &Element) -> Result<PathStep, PathError> {
        let annot = self.parse_annotations(step.annotations())?;
        let step = self.parse_step(step.value())?;
        Ok(PathStep(annot, step))
    }

    fn parse_annotations(&self, annot: &Annotations) -> Result<AnnotationMatch, PathError> {
        // TODO case sensitivity?
        fn parse_annot(a: &Symbol) -> Result<StringMatch, PathError> {
            Ok(StringMatch::Sensitive(a.text_or_error()?.to_string()))
        }
        annot.iter().map(parse_annot).collect()
    }

    fn parse_step(&self, value: &Value) -> Result<Step, PathError> {
        fn parse_str_step(s: &str) -> Step {
            // TODO case sensitivity?
            match s {
                "*" => Step::WildCard(),
                other => Step::Field(StringMatch::Sensitive(other.to_string())),
            }
        }
        Ok(match value {
            Value::Int(i) => {
                // TODO check i
                Step::Index(i.as_i64().expect("i64") as usize)
            }
            Value::Symbol(sym) => {
                let txt = sym.text().expect("sym text");
                parse_str_step(txt)
            }
            Value::String(st) => {
                let txt = st.text();
                parse_str_step(txt)
            }
            _ => panic!("bad step"),
        })
    }
}

#[derive(Debug, Clone)]
struct Node {
    annot: AnnotationMatch,
    children: HashMap<Step, Node>,
    accepts: bool,
}

impl Default for Node {
    fn default() -> Self {
        Self::new(vec![], HashMap::new(), false)
    }
}

impl Node {
    pub fn new(annot: AnnotationMatch, children: HashMap<Step, Node>, accepts: bool) -> Self {
        Self {
            annot,
            children,
            accepts,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Matcher {
    root: Node,
}

#[derive(Debug, Clone)]
pub struct Builder {
    root: Node,
    parser: PathParser,
}

impl Builder {
    pub fn new() -> Builder {
        Self {
            root: Node::default(),
            parser: PathParser::default(),
        }
    }

    pub fn add_path(mut self, path: &str) -> Result<Self, PathError> {
        fn merge_path(node: &mut Node, steps: &[PathStep]) {
            fn merge_step<'n>(node: &'n mut Node, step: &PathStep) -> &'n mut Node {
                //TODO
                node.children.iter_mut().next().unwrap().1
            }

            if let Some((step, steps)) = steps.split_first() {
                let next = merge_step(node, step);
                merge_path(next, steps)
            } else {
                node.accepts = true;
            }
        }

        let steps = self.parser.parse_path(path)?;
        dbg!(&steps);
        println!("{}", steps);

        merge_path(&mut self.root, steps.0.as_slice());
        dbg!(&self.root);
        /*
        self.root = match self.root.take() {
            None => Some(parsed),
            Some(root) => Some(root.merge(parsed)),
        };

        Ok(self)

         */
        Ok(self)
    }

    pub fn build(self) -> Result<Matcher, PathError> {
        let root = Node::default();
        Ok(Matcher { root })
    }

    // fn merge(node: Node, )
}

#[cfg(test)]
mod tests {
    use crate::ion_path_extractor::ui::Builder;

    #[track_caller]
    fn assert_paths(searchPaths: &[&str]) {
        //let mut builder = Builder::new();
        //for s in searchPaths {
        //    builder = builder.add_path(s).expect("add_path");
        // }
        //let res = builder.build();
        //assert!(res.is_ok());
    }

    #[track_caller]
    fn assert_path(searchPath: &str) {
        assert_paths(&[searchPath])
    }

    #[test]
    fn pathy() {
        assert_path("(foo * bar)");
    }
}
