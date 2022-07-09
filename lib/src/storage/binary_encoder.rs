use crate::storage::numeric_encoder::{EncodedQuad, EncodedTerm, EncodedTriple, StrHash};
use crate::storage::small_string::SmallString;
use crate::storage::StorageError;
use crate::store::CorruptionError;
use crate::extendedTree::{MultiTree, MultiTreeNode, extendedTreeNode};
use crate::extendedTree::vocab::{rdf, rdfs, owl, lubm};
use crate::xsd::*;
use std::collections::HashMap;
use std::io::{Cursor, Read};
use std::mem::size_of;
use std::rc::Rc;

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

pub static ATOM_BYTES: AtomicUsize = AtomicUsize::new(0);

#[cfg(not(target_arch = "wasm32"))]
pub const LATEST_STORAGE_VERSION: u64 = 1;
pub const WRITTEN_TERM_MAX_SIZE: usize = size_of::<u8>() + 2 * size_of::<StrHash>();
pub const INTERVAL_ENCODING_MAX_SIZE: usize = size_of::<u8>() * 19;

// Encoded term type blocks
// 1-7: usual named nodes (except prefixes c.f. later)
// 8-15: blank nodes
// 16-47: literals
// 48-55: triples
// 56-64: future use
// 64-127: default named node prefixes
// 128-255: custom named node prefixes
const TYPE_NAMED_NODE_ID: u8 = 1;
const TYPE_NUMERICAL_BLANK_NODE_ID: u8 = 8;
const TYPE_SMALL_BLANK_NODE_ID: u8 = 9;
const TYPE_BIG_BLANK_NODE_ID: u8 = 10;
const TYPE_SMALL_STRING_LITERAL: u8 = 16;
const TYPE_BIG_STRING_LITERAL: u8 = 17;
const TYPE_SMALL_SMALL_LANG_STRING_LITERAL: u8 = 20;
const TYPE_SMALL_BIG_LANG_STRING_LITERAL: u8 = 21;
const TYPE_BIG_SMALL_LANG_STRING_LITERAL: u8 = 22;
const TYPE_BIG_BIG_LANG_STRING_LITERAL: u8 = 23;
const TYPE_SMALL_TYPED_LITERAL: u8 = 24;
const TYPE_BIG_TYPED_LITERAL: u8 = 25;
const TYPE_BOOLEAN_LITERAL_TRUE: u8 = 28;
const TYPE_BOOLEAN_LITERAL_FALSE: u8 = 29;
const TYPE_FLOAT_LITERAL: u8 = 30;
const TYPE_DOUBLE_LITERAL: u8 = 31;
const TYPE_INTEGER_LITERAL: u8 = 32;
const TYPE_DECIMAL_LITERAL: u8 = 33;
const TYPE_DATE_TIME_LITERAL: u8 = 34;
const TYPE_TIME_LITERAL: u8 = 35;
const TYPE_DATE_LITERAL: u8 = 36;
const TYPE_G_YEAR_MONTH_LITERAL: u8 = 37;
const TYPE_G_YEAR_LITERAL: u8 = 38;
const TYPE_G_MONTH_DAY_LITERAL: u8 = 39;
const TYPE_G_DAY_LITERAL: u8 = 40;
const TYPE_G_MONTH_LITERAL: u8 = 41;
const TYPE_DURATION_LITERAL: u8 = 42;
const TYPE_YEAR_MONTH_DURATION_LITERAL: u8 = 43;
const TYPE_DAY_TIME_DURATION_LITERAL: u8 = 44;
const TYPE_TRIPLE: u8 = 48;

const TYPE_CLASS: u8 = 50;
const TYPE_PROPERTY: u8 = 51;

#[derive(Clone, Copy)]
pub enum QuadEncoding {
    Spog,
    Posg,
    Ospg,
    Gspo,
    Gpos,
    Gosp,
    Dspo,
    Dpos,
    Dosp,
}

impl QuadEncoding {
    // 将 buffer 包装进 Cursor里，然后可以调用cursor中的方法进行快速处理
    pub fn decode(self, buffer: &[u8]) -> Result<EncodedQuad, StorageError> {
        // 标准库在通常用作buffer(缓冲区)的各种类型上实现了一些 I/O traits，例如 Cursor<Vec<u8>> and Cursor<&[u8]>
        // Cursor 实现了 Read trait
        let mut cursor = Cursor::new(&buffer);   // 创建一个新的cursor来包装所提供的底层内存缓冲区
        
        match self {
            QuadEncoding::Spog => cursor.read_spog_quad(),
            QuadEncoding::Posg => cursor.read_posg_quad(),
            QuadEncoding::Ospg => cursor.read_ospg_quad(),
            QuadEncoding::Gspo => cursor.read_gspo_quad(),
            QuadEncoding::Gpos => cursor.read_gpos_quad(),
            QuadEncoding::Gosp => cursor.read_gosp_quad(),
            QuadEncoding::Dspo => cursor.read_dspo_quad(),
            QuadEncoding::Dpos => cursor.read_dpos_quad(),
            QuadEncoding::Dosp => cursor.read_dosp_quad(),
        }
    }
}

// 将内存里的 buffer 解码成 EncodedTerm
pub fn decode_term(buffer: &[u8]) -> Result<EncodedTerm, StorageError> {
    Cursor::new(&buffer).read_term()
}

pub trait TermReader {
    fn read_term(&mut self) -> Result<EncodedTerm, StorageError>;

    fn read_spog_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        let graph_name = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_posg_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        let subject = self.read_term()?;
        let graph_name = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_ospg_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let object = self.read_term()?;
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        let graph_name = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_gspo_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let graph_name = self.read_term()?;
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_gpos_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let graph_name = self.read_term()?;
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        let subject = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_gosp_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let graph_name = self.read_term()?;
        let object = self.read_term()?;
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name,
        })
    }

    fn read_dspo_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name: EncodedTerm::DefaultGraph,
        })
    }

    fn read_dpos_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let predicate = self.read_term()?;
        let object = self.read_term()?;
        let subject = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name: EncodedTerm::DefaultGraph,
        })
    }

    fn read_dosp_quad(&mut self) -> Result<EncodedQuad, StorageError> {
        let object = self.read_term()?;
        let subject = self.read_term()?;
        let predicate = self.read_term()?;
        Ok(EncodedQuad {
            subject,
            predicate,
            object,
            graph_name: EncodedTerm::DefaultGraph,
        })
    }
}

// 盲猜是从 column family里中将key读取出来然后进行解析


// Read trait 允许从源读取字节，Read trait 的实现者称为 ‘readers’
// Readers 由一种必需的方法 read() 定义。对 read() 的每次调用都会尝试将字节从此源拉入提供的buffer
// 为实现了 Read trait 的类型实现 TermReader，在其内部对 read_term() 方法进行实现
impl<R: Read> TermReader for R {
    // self 是装配了buffer字节数组的cursor
    fn read_term(&mut self) -> Result<EncodedTerm, StorageError> {
        let mut type_buffer = [0];  
        self.read_exact(&mut type_buffer)?;  // 该函数读取所需的字节数以完全填充指定的缓冲区 buff（在这里是类型buffer，只占一个字节）
        
        match type_buffer[0] {
            TYPE_NAMED_NODE_ID => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::NamedNode {
                    iri_id: StrHash::from_be_bytes(buffer),
                })
            }
            TYPE_NUMERICAL_BLANK_NODE_ID => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::NumericalBlankNode {
                    id: u128::from_be_bytes(buffer),
                })
            }
            TYPE_SMALL_BLANK_NODE_ID => {  // inner: [u8; 16]
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::SmallBlankNode(
                    SmallString::from_be_bytes(buffer).map_err(CorruptionError::new)?,
                ))
            }
            TYPE_BIG_BLANK_NODE_ID => { // StrHash
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::BigBlankNode {
                    id_id: StrHash::from_be_bytes(buffer),
                })
            }
            TYPE_SMALL_SMALL_LANG_STRING_LITERAL => { // language解析在前
                let mut language_buffer = [0; 16];
                self.read_exact(&mut language_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::SmallSmallLangStringLiteral {
                    value: SmallString::from_be_bytes(value_buffer)
                        .map_err(CorruptionError::new)?,
                    language: SmallString::from_be_bytes(language_buffer)
                        .map_err(CorruptionError::new)?,
                })
            }
            TYPE_SMALL_BIG_LANG_STRING_LITERAL => {
                let mut language_buffer = [0; 16];
                self.read_exact(&mut language_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::SmallBigLangStringLiteral {
                    value: SmallString::from_be_bytes(value_buffer)
                        .map_err(CorruptionError::new)?,
                    language_id: StrHash::from_be_bytes(language_buffer),
                })
            }
            TYPE_BIG_SMALL_LANG_STRING_LITERAL => {
                let mut language_buffer = [0; 16];
                self.read_exact(&mut language_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::BigSmallLangStringLiteral {
                    value_id: StrHash::from_be_bytes(value_buffer),
                    language: SmallString::from_be_bytes(language_buffer)
                        .map_err(CorruptionError::new)?,
                })
            }
            TYPE_BIG_BIG_LANG_STRING_LITERAL => {
                let mut language_buffer = [0; 16];
                self.read_exact(&mut language_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::BigBigLangStringLiteral {
                    value_id: StrHash::from_be_bytes(value_buffer),
                    language_id: StrHash::from_be_bytes(language_buffer),
                })
            }
            TYPE_SMALL_TYPED_LITERAL => {
                let mut datatype_buffer = [0; 16]; // NamedNodeRef
                self.read_exact(&mut datatype_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::SmallTypedLiteral {
                    datatype_id: StrHash::from_be_bytes(datatype_buffer),
                    value: SmallString::from_be_bytes(value_buffer)
                        .map_err(CorruptionError::new)?,
                })
            }
            TYPE_BIG_TYPED_LITERAL => {
                let mut datatype_buffer = [0; 16];
                self.read_exact(&mut datatype_buffer)?;
                let mut value_buffer = [0; 16];
                self.read_exact(&mut value_buffer)?;
                Ok(EncodedTerm::BigTypedLiteral {
                    datatype_id: StrHash::from_be_bytes(datatype_buffer),
                    value_id: StrHash::from_be_bytes(value_buffer),
                })
            }
            TYPE_SMALL_STRING_LITERAL => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::SmallStringLiteral(
                    SmallString::from_be_bytes(buffer).map_err(CorruptionError::new)?,
                ))
            }
            TYPE_BIG_STRING_LITERAL => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::BigStringLiteral {
                    value_id: StrHash::from_be_bytes(buffer),
                })
            }
            TYPE_BOOLEAN_LITERAL_TRUE => Ok(EncodedTerm::BooleanLiteral(true)),
            TYPE_BOOLEAN_LITERAL_FALSE => Ok(EncodedTerm::BooleanLiteral(false)),
            TYPE_FLOAT_LITERAL => {
                let mut buffer = [0; 4];   // 32位
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::FloatLiteral(Float::from_be_bytes(buffer)))
            }
            TYPE_DOUBLE_LITERAL => {
                let mut buffer = [0; 8];  // 64位
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DoubleLiteral(Double::from_be_bytes(buffer)))
            }
            TYPE_INTEGER_LITERAL => {
                let mut buffer = [0; 8]; // i64
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::IntegerLiteral(i64::from_be_bytes(buffer)))
            }
            TYPE_DECIMAL_LITERAL => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DecimalLiteral(Decimal::from_be_bytes(buffer)))
            }
            TYPE_DATE_TIME_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DateTimeLiteral(DateTime::from_be_bytes(
                    buffer,
                )))
            }
            TYPE_TIME_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::TimeLiteral(Time::from_be_bytes(buffer)))
            }
            TYPE_DATE_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DateLiteral(Date::from_be_bytes(buffer)))
            }
            TYPE_G_YEAR_MONTH_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::GYearMonthLiteral(GYearMonth::from_be_bytes(
                    buffer,
                )))
            }
            TYPE_G_YEAR_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::GYearLiteral(GYear::from_be_bytes(buffer)))
            }
            TYPE_G_MONTH_DAY_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::GMonthDayLiteral(GMonthDay::from_be_bytes(
                    buffer,
                )))
            }
            TYPE_G_DAY_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::GDayLiteral(GDay::from_be_bytes(buffer)))
            }
            TYPE_G_MONTH_LITERAL => {
                let mut buffer = [0; 18];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::GMonthLiteral(GMonth::from_be_bytes(buffer)))
            }
            TYPE_DURATION_LITERAL => {
                let mut buffer = [0; 24];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DurationLiteral(Duration::from_be_bytes(
                    buffer,
                )))
            }
            TYPE_YEAR_MONTH_DURATION_LITERAL => {
                let mut buffer = [0; 8];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::YearMonthDurationLiteral(
                    YearMonthDuration::from_be_bytes(buffer),
                ))
            }
            TYPE_DAY_TIME_DURATION_LITERAL => {
                let mut buffer = [0; 16];
                self.read_exact(&mut buffer)?;
                Ok(EncodedTerm::DayTimeDurationLiteral(
                    DayTimeDuration::from_be_bytes(buffer),
                ))
            }
            TYPE_TRIPLE => Ok(EncodedTerm::Triple(Rc::new(EncodedTriple {
                subject: self.read_term()?,
                predicate: self.read_term()?,
                object: self.read_term()?,
            }))),
            _ => Err(CorruptionError::msg("the term buffer has an invalid type id").into()),
        }
    }
}

pub fn write_spog_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
    write_term(sink, &quad.graph_name);
}

pub fn write_posg_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
    write_term(sink, &quad.graph_name);
}

pub fn write_ospg_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.graph_name);
}

pub fn write_gspo_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.graph_name);
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
}

pub fn write_gpos_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.graph_name);
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
}

pub fn write_gosp_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.graph_name);
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
}

pub fn write_spo_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
}

pub fn write_pos_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.predicate);
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
}

pub fn write_osp_quad(sink: &mut Vec<u8>, quad: &EncodedQuad) {
    write_term(sink, &quad.object);
    write_term(sink, &quad.subject);
    write_term(sink, &quad.predicate);
}

// 分别编码 一 二 三 四 个EncodedTerm
pub fn encode_term(t: &EncodedTerm) -> Vec<u8> {
    let mut vec = Vec::with_capacity(WRITTEN_TERM_MAX_SIZE);   // 创建一个具有指定容量的 vector
    write_term(&mut vec, t);
    vec
}

pub fn encode_term_pair(t1: &EncodedTerm, t2: &EncodedTerm) -> Vec<u8> {
    let mut vec = Vec::with_capacity(2 * WRITTEN_TERM_MAX_SIZE);
    write_term(&mut vec, t1);
    write_term(&mut vec, t2);
    vec
}



pub fn encode_term_triple(t1: &EncodedTerm, t2: &EncodedTerm, t3: &EncodedTerm) -> Vec<u8> {
    let mut vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    write_term(&mut vec, t1);
    write_term(&mut vec, t2);
    write_term(&mut vec, t3);

    ATOM_BYTES.fetch_add(vec.capacity(), Ordering::SeqCst);
    vec
}


// ############################## 将区间编码加在value中 ##############################
pub fn encode_term_triple_oxiuse_value_spo(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> (Vec<u8>, Vec<u8>) {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的
    // 编码 key
    write_term(&mut key_vec, map.get("s").unwrap());
    write_term(&mut key_vec, map.get("p").unwrap());
    write_term(&mut key_vec, map.get("o").unwrap());

    ATOM_BYTES.fetch_add(key_vec.capacity(), Ordering::SeqCst);
    ATOM_BYTES.fetch_add(value_vec.capacity(), Ordering::SeqCst);
    // println!("语义数据库占用内存空间: {}", ATOM_BYTES.load(Ordering::SeqCst));

    (key_vec , value_vec)
}

pub fn encode_term_triple_oxiuse_value_pos(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> (Vec<u8>, Vec<u8>) {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    // 编码 key
    write_term(&mut key_vec, map.get("p").unwrap());
    write_term(&mut key_vec, map.get("o").unwrap());
    write_term(&mut key_vec, map.get("s").unwrap());

    ATOM_BYTES.fetch_add(key_vec.capacity(), Ordering::SeqCst);
    ATOM_BYTES.fetch_add(value_vec.capacity(), Ordering::SeqCst);
    // println!("语义数据库占用内存空间: {}", ATOM_BYTES.load(Ordering::SeqCst));

    (key_vec , value_vec)
}

pub fn encode_term_triple_oxiuse_value_osp(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> (Vec<u8>, Vec<u8>) {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    // 编码 key
    write_term(&mut key_vec, map.get("o").unwrap());
    write_term(&mut key_vec, map.get("s").unwrap());
    write_term(&mut key_vec, map.get("p").unwrap());

    ATOM_BYTES.fetch_add(key_vec.capacity(), Ordering::SeqCst);
    ATOM_BYTES.fetch_add(value_vec.capacity(), Ordering::SeqCst);

    (key_vec , value_vec)
}


pub fn encode_term_triple_oxiuse_key_spo(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> Vec<u8> {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let mut value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    key_vec.append(&mut value_vec);

    // 编码 key
    write_term(&mut key_vec, map.get("s").unwrap());
    write_term(&mut key_vec, map.get("p").unwrap());
    write_term(&mut key_vec, map.get("o").unwrap());

    key_vec
}

pub fn encode_term_triple_oxiuse_key_pos(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> Vec<u8> {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let mut value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    key_vec.append(&mut value_vec);

    // 编码 key
    write_term(&mut key_vec, map.get("p").unwrap());
    write_term(&mut key_vec, map.get("o").unwrap());
    write_term(&mut key_vec, map.get("s").unwrap());

    key_vec
}

pub fn encode_term_triple_oxiuse_key_osp(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> Vec<u8> {
    let mut key_vec = Vec::with_capacity(3 * WRITTEN_TERM_MAX_SIZE);
    let mut value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    key_vec.append(&mut value_vec);

    // 编码 key
    write_term(&mut key_vec, map.get("o").unwrap());
    write_term(&mut key_vec, map.get("s").unwrap());
    write_term(&mut key_vec, map.get("p").unwrap());

    key_vec
}

// ############################## 将区间编码加在key中 ##############################
pub fn encode_term_triple_oxiuse_key(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> Vec<u8>{
    let mut key_vec = Vec::with_capacity(5 * WRITTEN_TERM_MAX_SIZE);
    let mut value_vec = encoded_interval_encoding(map.clone(), trees);   // 获得区间编码，有可能是空的

    println!("{:?}", value_vec);

    // 编码 key
    write_term(&mut key_vec, map.get("s").unwrap());
    write_term(&mut key_vec, map.get("p").unwrap());
    write_term(&mut key_vec, map.get("o").unwrap());

    key_vec.append(&mut value_vec);
    key_vec
}

// TODO:区间编码的方案在这，然后将编码的vec返回
fn encoded_interval_encoding(map: HashMap<&str, &EncodedTerm>, trees: (MultiTree, MultiTree)) -> Vec<u8> { 
    let mut value_vec = Vec::with_capacity(INTERVAL_ENCODING_MAX_SIZE);   // 这个大小可能得改

    let classTree = trees.0;
    let propertyTree = trees.1;

    let sub_class_of = StrHash::new(rdfs::SUB_CLASS_OF);
    let sub_property_of = StrHash::new(rdfs::SUB_PROPERTY_OF);
    let domain = StrHash::new(rdfs::DOMAIN);
    let range = StrHash::new(rdfs::RANGE);
    let rdf_type = StrHash::new(rdf::TYPE);
    let sub_organization_of = StrHash::new(lubm::SUB_ORGANIZATION);

    match map.get("p").unwrap() {
        EncodedTerm::NamedNode { iri_id } => {
            if *iri_id == sub_class_of || *iri_id == sub_organization_of{   // 子父类的情况，需要先得到子父类（父节点编码的是第一个区间编码）
                // 先得到主语和宾语
                let s = {
                    if let EncodedTerm::NamedNode { iri_id } = map.get("s").unwrap() {
                        classTree.get_node_by_strhash(*iri_id)
                    } else {
                        Err(())
                    }
                };

                let o = {
                    if let EncodedTerm::NamedNode { iri_id } = map.get("o").unwrap() {
                        classTree.get_node_by_strhash(*iri_id)
                    } else {
                        Err(())
                    }
                };

                match s {
                    Ok(child) => {
                        match o {
                            Ok(parent) => {
                                value_vec.push(TYPE_CLASS);

                                for interval in child.get_interval_nodes().iter() {
                                    if interval.get_parent().unwrap().get_data() == parent.get_data() {
                                        value_vec.extend_from_slice(&interval.get_start().to_be_bytes());
                                        value_vec.extend_from_slice(&interval.get_end().to_be_bytes());
                                    }
                                }

                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_start().to_be_bytes());
                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_end().to_be_bytes());
                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_layer().to_be_bytes());
                            },
                            _ => return value_vec
                        }   
                    },
                    _ => return value_vec
                };
            } else if *iri_id == sub_property_of {   // 子父属性
                // 先得到主语和宾语
                let s = {
                    if let EncodedTerm::NamedNode { iri_id } = map.get("s").unwrap() {
                        propertyTree.get_node_by_strhash(*iri_id)
                    } else {
                        Err(())
                    }
                };

                let o = {
                    if let EncodedTerm::NamedNode { iri_id } = map.get("o").unwrap() {
                        propertyTree.get_node_by_strhash(*iri_id)
                    } else {
                        Err(())
                    }
                };

                match s {
                    Ok(child) => {
                        match o {
                            Ok(parent) => {
                                value_vec.push(TYPE_PROPERTY);

                                for interval in child.get_interval_nodes().iter() {
                                    if interval.get_parent().unwrap().get_data() == parent.get_data() {
                                        value_vec.extend_from_slice(&interval.get_start().to_be_bytes());
                                        value_vec.extend_from_slice(&interval.get_end().to_be_bytes());
                                    }
                                }

                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_start().to_be_bytes());
                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_end().to_be_bytes());
                                value_vec.extend_from_slice(&parent.get_interval_nodes().get(0).unwrap().get_layer().to_be_bytes());
                            },
                            _ => return value_vec
                        }   
                    },
                    _ => return value_vec
                };
            } else if (*iri_id == domain) || (*iri_id == range) || (*iri_id == rdf_type){   // domain、range、type
                
                let o = {
                    if let EncodedTerm::NamedNode { iri_id } = map.get("o").unwrap() {
                        classTree.get_node_by_strhash(*iri_id)
                    } else {
                        Err(())
                    }
                };

                match o {
                    Ok(node) => {
                        value_vec.push(TYPE_CLASS);
                        let count = node.get_interval_nodes().len() as u8;
                        value_vec.extend_from_slice(&count.to_be_bytes());

                        for interval in node.get_interval_nodes().iter() {
                            value_vec.extend_from_slice(&interval.get_start().to_be_bytes());
                            value_vec.extend_from_slice(&interval.get_end().to_be_bytes());
                            value_vec.extend_from_slice(&interval.get_layer().to_be_bytes());
                        }
                    },
                    _ => return value_vec
                }
            }
        },
        _ => {}
    }


    value_vec
}

pub fn encode_term_quad(
    t1: &EncodedTerm,
    t2: &EncodedTerm,
    t3: &EncodedTerm,
    t4: &EncodedTerm,
) -> Vec<u8> {
    let mut vec = Vec::with_capacity(4 * WRITTEN_TERM_MAX_SIZE);
    write_term(&mut vec, t1);
    write_term(&mut vec, t2);
    write_term(&mut vec, t3);
    write_term(&mut vec, t4);
    vec
}

// 将传入的 term 类型 id 以及 term 的字节序列放入 buffer 中
pub fn write_term(sink: &mut Vec<u8>, term: &EncodedTerm) {
    match term {
        EncodedTerm::DefaultGraph => (),
        EncodedTerm::NamedNode { iri_id } => {
            sink.push(TYPE_NAMED_NODE_ID);
            sink.extend_from_slice(&iri_id.to_be_bytes());
        }
        EncodedTerm::NumericalBlankNode { id } => {
            sink.push(TYPE_NUMERICAL_BLANK_NODE_ID);
            sink.extend_from_slice(&id.to_be_bytes())
        }
        EncodedTerm::SmallBlankNode(id) => {
            sink.push(TYPE_SMALL_BLANK_NODE_ID);
            sink.extend_from_slice(&id.to_be_bytes())
        }
        EncodedTerm::BigBlankNode { id_id } => {
            sink.push(TYPE_BIG_BLANK_NODE_ID);
            sink.extend_from_slice(&id_id.to_be_bytes());
        }
        EncodedTerm::SmallStringLiteral(value) => {
            sink.push(TYPE_SMALL_STRING_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::BigStringLiteral { value_id } => {
            sink.push(TYPE_BIG_STRING_LITERAL);
            sink.extend_from_slice(&value_id.to_be_bytes());
        }
        EncodedTerm::SmallSmallLangStringLiteral { value, language } => {
            sink.push(TYPE_SMALL_SMALL_LANG_STRING_LITERAL);
            sink.extend_from_slice(&language.to_be_bytes());
            sink.extend_from_slice(&value.to_be_bytes());
        }
        EncodedTerm::SmallBigLangStringLiteral { value, language_id } => {
            sink.push(TYPE_SMALL_BIG_LANG_STRING_LITERAL);
            sink.extend_from_slice(&language_id.to_be_bytes());
            sink.extend_from_slice(&value.to_be_bytes());
        }
        EncodedTerm::BigSmallLangStringLiteral { value_id, language } => {
            sink.push(TYPE_BIG_SMALL_LANG_STRING_LITERAL);
            sink.extend_from_slice(&language.to_be_bytes());
            sink.extend_from_slice(&value_id.to_be_bytes());
        }
        EncodedTerm::BigBigLangStringLiteral {
            value_id,
            language_id,
        } => {
            sink.push(TYPE_BIG_BIG_LANG_STRING_LITERAL);
            sink.extend_from_slice(&language_id.to_be_bytes());
            sink.extend_from_slice(&value_id.to_be_bytes());
        }
        EncodedTerm::SmallTypedLiteral { value, datatype_id } => {
            sink.push(TYPE_SMALL_TYPED_LITERAL);
            sink.extend_from_slice(&datatype_id.to_be_bytes());
            sink.extend_from_slice(&value.to_be_bytes());
        }
        EncodedTerm::BigTypedLiteral {
            value_id,
            datatype_id,
        } => {
            sink.push(TYPE_BIG_TYPED_LITERAL);
            sink.extend_from_slice(&datatype_id.to_be_bytes());
            sink.extend_from_slice(&value_id.to_be_bytes());
        }
        EncodedTerm::BooleanLiteral(true) => sink.push(TYPE_BOOLEAN_LITERAL_TRUE),
        EncodedTerm::BooleanLiteral(false) => sink.push(TYPE_BOOLEAN_LITERAL_FALSE),
        EncodedTerm::FloatLiteral(value) => {
            sink.push(TYPE_FLOAT_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DoubleLiteral(value) => {
            sink.push(TYPE_DOUBLE_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::IntegerLiteral(value) => {
            sink.push(TYPE_INTEGER_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DecimalLiteral(value) => {
            sink.push(TYPE_DECIMAL_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DateTimeLiteral(value) => {
            sink.push(TYPE_DATE_TIME_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::TimeLiteral(value) => {
            sink.push(TYPE_TIME_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DurationLiteral(value) => {
            sink.push(TYPE_DURATION_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DateLiteral(value) => {
            sink.push(TYPE_DATE_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::GYearMonthLiteral(value) => {
            sink.push(TYPE_G_YEAR_MONTH_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::GYearLiteral(value) => {
            sink.push(TYPE_G_YEAR_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::GMonthDayLiteral(value) => {
            sink.push(TYPE_G_MONTH_DAY_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::GDayLiteral(value) => {
            sink.push(TYPE_G_DAY_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::GMonthLiteral(value) => {
            sink.push(TYPE_G_MONTH_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::YearMonthDurationLiteral(value) => {
            sink.push(TYPE_YEAR_MONTH_DURATION_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::DayTimeDurationLiteral(value) => {
            sink.push(TYPE_DAY_TIME_DURATION_LITERAL);
            sink.extend_from_slice(&value.to_be_bytes())
        }
        EncodedTerm::Triple(value) => {
            sink.push(TYPE_TRIPLE);
            write_term(sink, &value.subject);
            write_term(sink, &value.predicate);
            write_term(sink, &value.object);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::TermRef;
    use crate::storage::numeric_encoder::*;
    use std::cell::RefCell;
    use std::collections::HashMap;

    #[derive(Default)]
    struct MemoryStrStore {
        id2str: RefCell<HashMap<StrHash, String>>,
    }

    impl StrLookup for MemoryStrStore {
        fn get_str(&self, key: &StrHash) -> Result<Option<String>, StorageError> {
            Ok(self.id2str.borrow().get(key).cloned())
        }

        fn contains_str(&self, key: &StrHash) -> Result<bool, StorageError> {
            Ok(self.id2str.borrow().contains_key(key))
        }
    }

    impl MemoryStrStore {
        fn insert_term(&self, term: TermRef<'_>, encoded: &EncodedTerm) {
            insert_term(term, encoded, &mut |h, v| {
                self.insert_str(h, v);
                Ok(())
            })
            .unwrap();
        }

        fn insert_str(&self, key: &StrHash, value: &str) {
            self.id2str
                .borrow_mut()
                .entry(*key)
                .or_insert_with(|| value.to_owned());
        }
    }

    #[test]
    fn test_encoding() {
        use crate::model::vocab::xsd;
        use crate::model::*;

        let store = MemoryStrStore::default();
        let terms: Vec<Term> = vec![
            NamedNode::new_unchecked("http://foo.com").into(),
            NamedNode::new_unchecked("http://bar.com").into(),
            NamedNode::new_unchecked("http://foo.com").into(),
            BlankNode::default().into(),
            BlankNode::new_unchecked("bnode").into(),
            BlankNode::new_unchecked("foo-bnode-thisisaverylargeblanknode").into(),
            Literal::new_simple_literal("literal").into(),
            BlankNode::new_unchecked("foo-literal-thisisaverylargestringliteral").into(),
            Literal::from(true).into(),
            Literal::from(1.2).into(),
            Literal::from(1).into(),
            Literal::from("foo-string").into(),
            Literal::new_language_tagged_literal_unchecked("foo-fr", "fr").into(),
            Literal::new_language_tagged_literal_unchecked(
                "foo-fr-literal-thisisaverylargelanguagetaggedstringliteral",
                "fr",
            )
            .into(),
            Literal::new_language_tagged_literal_unchecked(
                "foo-big",
                "fr-FR-Latn-x-foo-bar-baz-bat-aaaa-bbbb-cccc",
            )
            .into(),
            Literal::new_language_tagged_literal_unchecked(
                "foo-big-literal-thisisaverylargelanguagetaggedstringliteral",
                "fr-FR-Latn-x-foo-bar-baz-bat-aaaa-bbbb-cccc",
            )
            .into(),
            Literal::new_typed_literal("-1.32", xsd::DECIMAL).into(),
            Literal::new_typed_literal("2020-01-01T01:01:01Z", xsd::DATE_TIME).into(),
            Literal::new_typed_literal("2020-01-01", xsd::DATE).into(),
            Literal::new_typed_literal("01:01:01Z", xsd::TIME).into(),
            Literal::new_typed_literal("2020-01", xsd::G_YEAR_MONTH).into(),
            Literal::new_typed_literal("2020", xsd::G_YEAR).into(),
            Literal::new_typed_literal("--01-01", xsd::G_MONTH_DAY).into(),
            Literal::new_typed_literal("--01", xsd::G_MONTH).into(),
            Literal::new_typed_literal("---01", xsd::G_DAY).into(),
            Literal::new_typed_literal("PT1S", xsd::DURATION).into(),
            Literal::new_typed_literal("PT1S", xsd::DAY_TIME_DURATION).into(),
            Literal::new_typed_literal("P1Y", xsd::YEAR_MONTH_DURATION).into(),
            Literal::new_typed_literal("-foo", NamedNode::new_unchecked("http://foo.com")).into(),
            Literal::new_typed_literal(
                "-foo-thisisaverybigtypedliteralwiththefoodatatype",
                NamedNode::new_unchecked("http://foo.com"),
            )
            .into(),
            Triple::new(
                NamedNode::new_unchecked("http://foo.com"),
                NamedNode::new_unchecked("http://bar.com"),
                Literal::from(true),
            )
            .into(),
        ];
        for term in terms {
            let encoded = term.as_ref().into();
            store.insert_term(term.as_ref(), &encoded);
            assert_eq!(encoded, term.as_ref().into());
            assert_eq!(term, store.decode_term(&encoded).unwrap());

            let mut buffer = Vec::new();
            write_term(&mut buffer, &encoded);
            assert_eq!(encoded, Cursor::new(&buffer).read_term().unwrap());
        }
    }
}
