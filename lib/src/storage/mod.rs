use crate::model::{GraphNameRef, NamedOrBlankNodeRef, Quad, QuadRef, TermRef};
use crate::storage::backend::{Reader, Transaction};
#[cfg(not(target_arch = "wasm32"))]
use crate::storage::binary_encoder::LATEST_STORAGE_VERSION;
use crate::storage::binary_encoder::{
    decode_term, encode_term, encode_term_pair, encode_term_quad, encode_term_triple,
    write_gosp_quad, write_gpos_quad, write_gspo_quad, write_osp_quad, write_ospg_quad,
    write_pos_quad, write_posg_quad, write_spo_quad, write_spog_quad, write_term, QuadEncoding,
    WRITTEN_TERM_MAX_SIZE,ATOM_BYTES
};
pub use crate::storage::error::{CorruptionError, LoaderError, SerializerError, StorageError};
use crate::storage::numeric_encoder::{
    insert_term, Decoder, EncodedQuad, EncodedTerm, StrHash, StrLookup,
};

use backend::{ColumnFamily, ColumnFamilyDefinition, Db, Iter};
use std::cmp::{max, min};
use std::collections::VecDeque;
#[cfg(not(target_arch = "wasm32"))]
use std::collections::{HashMap, HashSet};
use std::error::Error;
#[cfg(not(target_arch = "wasm32"))]
use std::mem::take;
use std::ops::Mul;
#[cfg(not(target_arch = "wasm32"))]
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::thread::spawn;
use std::thread::JoinHandle;
use sysinfo::{System, SystemExt};

use crate::extendedTree::vocab::{owl, rdf, rdfs, lubm};
use crate::extendedTree::{MultiTree};
use std::fs::File;
use std::io::{self, BufRead, Read};

use self::binary_encoder::{encode_term_triple_oxiuse_value_spo, encode_term_triple_oxiuse_value_osp, encode_term_triple_oxiuse_value_pos, encode_term_triple_oxiuse_key_spo, encode_term_triple_oxiuse_key_pos, encode_term_triple_oxiuse_key_osp};

mod backend;
mod binary_encoder;
mod error;
pub mod numeric_encoder;
pub mod small_string;

// columnfamily的名字
const ID2STR_CF: &str = "id2str";
const SPOG_CF: &str = "spog";
const POSG_CF: &str = "posg";
const OSPG_CF: &str = "ospg";
const GSPO_CF: &str = "gspo";
const GPOS_CF: &str = "gpos";
const GOSP_CF: &str = "gosp";
const DSPO_CF: &str = "dspo";
const DPOS_CF: &str = "dpos";
const DOSP_CF: &str = "dosp";
const GRAPHS_CF: &str = "graphs";
const DEFAULT_CF: &str = "default";
#[cfg(not(target_arch = "wasm32"))]
const DEFAULT_BULK_LOAD_BATCH_SIZE: usize = 1_000_000;
const MAX_BULK_LOAD_BATCH_SIZE: usize = 100_000_000;

/// Low level storage primitives
// columnfamily可以起到隔离数据的作用。下面除了九张表存储三元组（四元组）之外，还包括id2str映射表
#[derive(Clone)]
pub struct Storage {
    db: Db,

    default_cf: ColumnFamily,
    id2str_cf: ColumnFamily,
    spog_cf: ColumnFamily,
    posg_cf: ColumnFamily,
    ospg_cf: ColumnFamily,
    gspo_cf: ColumnFamily,
    gpos_cf: ColumnFamily,
    gosp_cf: ColumnFamily,
    dspo_cf: ColumnFamily,
    dpos_cf: ColumnFamily,
    dosp_cf: ColumnFamily,
    graphs_cf: ColumnFamily,
}

// 有column family、flash、compaction 对 rocksDB封装的底层操作
impl Storage {
    // 创建Storage
    pub fn new() -> Result<Self, StorageError> {
        Self::setup(Db::new(Self::initial_column_families())?)
    }

    // 打开给定路径的数据库
    #[cfg(not(target_arch = "wasm32"))]
    pub fn open(path: &Path) -> Result<Self, StorageError> {
        Self::setup(Db::open(path, Self::initial_column_families())?)
    }

    // 初始化列族参数，用此来创建Db实例
    fn initial_column_families() -> Vec<ColumnFamilyDefinition> {
        vec![
            ColumnFamilyDefinition {
                name: ID2STR_CF,
                use_iter: false,
                min_prefix_size: 0,
                unordered_writes: true,
            },
            ColumnFamilyDefinition {
                name: SPOG_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: POSG_CF,
                use_iter: true,
                min_prefix_size: 17, // named node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: OSPG_CF,
                use_iter: true,
                min_prefix_size: 0, // There are small literals...
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: GSPO_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: GPOS_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: GOSP_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: DSPO_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: DPOS_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: DOSP_CF,
                use_iter: true,
                min_prefix_size: 0, // There are small literals...
                unordered_writes: false,
            },
            ColumnFamilyDefinition {
                name: GRAPHS_CF,
                use_iter: true,
                min_prefix_size: 17, // named or blank node start
                unordered_writes: false,
            },
        ]
    }

    // 根据cf名获得cf(rocksdb.rs)，应该是对各个 column family 进行了包装（或者其它什么操作）
    // 接着再使用db实例以及这些cf创建Storage实例
    // 装配 columnfamily
    fn setup(db: Db) -> Result<Self, StorageError> {
        let this = Self {
            default_cf: db.column_family(DEFAULT_CF).unwrap(),   
            id2str_cf: db.column_family(ID2STR_CF).unwrap(),
            spog_cf: db.column_family(SPOG_CF).unwrap(),
            posg_cf: db.column_family(POSG_CF).unwrap(),
            ospg_cf: db.column_family(OSPG_CF).unwrap(),
            gspo_cf: db.column_family(GSPO_CF).unwrap(),
            gpos_cf: db.column_family(GPOS_CF).unwrap(),
            gosp_cf: db.column_family(GOSP_CF).unwrap(),
            dspo_cf: db.column_family(DSPO_CF).unwrap(),
            dpos_cf: db.column_family(DPOS_CF).unwrap(),
            dosp_cf: db.column_family(DOSP_CF).unwrap(),
            graphs_cf: db.column_family(GRAPHS_CF).unwrap(),
            db,
        };
        #[cfg(not(target_arch = "wasm32"))]
        this.migrate()?;
        Ok(this)
    }

    // 数据迁移
    #[cfg(not(target_arch = "wasm32"))]
    fn migrate(&self) -> Result<(), StorageError> {
        let mut version = self.ensure_version()?;
        if version == 0 {
            // We migrate to v1
            let mut graph_names = HashSet::new();
            for quad in self.snapshot().quads() {
                let quad = quad?;
                if !quad.graph_name.is_default_graph() {   // 不是默认图则放进去
                    graph_names.insert(quad.graph_name);
                }
            }
            let mut graph_names = graph_names
                .into_iter()
                .map(|g| encode_term(&g))
                .collect::<Vec<_>>();
            graph_names.sort_unstable();
            let mut stt_file = self.db.new_sst_file()?;
            for k in graph_names {
                stt_file.insert_empty(&k)?;
            }
            self.db
                .insert_stt_files(&[(&self.graphs_cf, stt_file.finish()?)])?;

            version = 1;
            self.update_version(version)?;
        }

        match version {
            _ if version < LATEST_STORAGE_VERSION => Err(CorruptionError::msg(format!(
                "The RocksDB database is using the outdated encoding version {}. Automated migration is not supported, please dump the store dataset using a compatible Oxigraph version and load it again using the current version",
                version
            )).into()),
            LATEST_STORAGE_VERSION => Ok(()),
            _ => Err(CorruptionError::msg(format!(
                "The RocksDB database is using the too recent version {}. Upgrade to the latest Oxigraph version to load this database",
                version
            )).into())
        }
    }

    // 读取当前的 oxversion（若不存在则写入 LATEST_STORAGE_VERSION）
    #[cfg(not(target_arch = "wasm32"))]
    fn ensure_version(&self) -> Result<u64, StorageError> {
        Ok(
            if let Some(version) = self.db.get(&self.default_cf, b"oxversion")? {   // 取出已经存在于 default_cf 上的 oxversion
                let mut buffer = [0; 8];
                buffer.copy_from_slice(&version);
                u64::from_be_bytes(buffer)
            } else {
                self.update_version(LATEST_STORAGE_VERSION)?;
                LATEST_STORAGE_VERSION
            },
        )
    }

    // 更新 version
    #[cfg(not(target_arch = "wasm32"))]
    fn update_version(&self, version: u64) -> Result<(), StorageError> {
        self.db
            .insert(&self.default_cf, b"oxversion", &version.to_be_bytes())?;
        self.db.flush(&self.default_cf)
    }

    // 创建当前Storage(db)的快照，并返回StorageReader【当前的Storage+一个只读视图（Reader）】
    pub fn snapshot(&self) -> StorageReader {
        StorageReader {
            reader: self.db.snapshot(),
            storage: self.clone(),
        }
    }

    // 开启事务？
    pub fn transaction<'a, 'b: 'a, T, E: Error + 'static + From<StorageError>>(
        &'b self,
        f: impl Fn(StorageWriter<'a>) -> Result<T, E>,
    ) -> Result<T, E> {
        self.db.transaction(|transaction| {
            f(StorageWriter {
                buffer: Vec::new(),
                transaction,
                storage: self,
            })
        })
    }

    // 最终数据的持久化都是保存在SST中，而SST则是由Memtable刷新到磁盘生成的，这就是Flush过程
    // 也使用了 rocksdb.rs 中提供的 API
    #[cfg(not(target_arch = "wasm32"))]
    pub fn flush(&self) -> Result<(), StorageError> {
        self.db.flush(&self.default_cf)?;
        self.db.flush(&self.gpos_cf)?;
        self.db.flush(&self.gpos_cf)?;
        self.db.flush(&self.gosp_cf)?;
        self.db.flush(&self.spog_cf)?;
        self.db.flush(&self.posg_cf)?;
        self.db.flush(&self.ospg_cf)?;
        self.db.flush(&self.dspo_cf)?;
        self.db.flush(&self.dpos_cf)?;
        self.db.flush(&self.dosp_cf)?;
        self.db.flush(&self.id2str_cf)
    }

    // 使用了 rocksdb.rs 中提供了API
    #[cfg(not(target_arch = "wasm32"))]
    pub fn compact(&self) -> Result<(), StorageError> {
        self.db.compact(&self.default_cf)?;
        self.db.compact(&self.gpos_cf)?;
        self.db.compact(&self.gpos_cf)?;
        self.db.compact(&self.gosp_cf)?;
        self.db.compact(&self.spog_cf)?;
        self.db.compact(&self.posg_cf)?;
        self.db.compact(&self.ospg_cf)?;
        self.db.compact(&self.dspo_cf)?;
        self.db.compact(&self.dpos_cf)?;
        self.db.compact(&self.dosp_cf)?;
        self.db.compact(&self.id2str_cf)
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub fn backup(&self, target_directory: &Path) -> Result<(), StorageError> {
        self.db.backup(target_directory)
    }
}
#[derive(Clone)]

pub struct StorageReader {
    reader: Reader,
    storage: Storage,   // 内
}

impl StorageReader {
    // 三元组的个数？
    pub fn len(&self) -> Result<usize, StorageError> {
        Ok(self.reader.len(&self.storage.gspo_cf)? + self.reader.len(&self.storage.dspo_cf)?)
    }

    pub fn is_empty(&self) -> Result<bool, StorageError> {
        Ok(self.reader.is_empty(&self.storage.gspo_cf)?
            && self.reader.is_empty(&self.storage.dspo_cf)?)
    }

    pub fn contains(&self, quad: &EncodedQuad) -> Result<bool, StorageError> {
        let mut buffer = Vec::with_capacity(4 * WRITTEN_TERM_MAX_SIZE);
        if quad.graph_name.is_default_graph() {
            write_spo_quad(&mut buffer, quad);
            Ok(self.reader.contains_key(&self.storage.dspo_cf, &buffer)?)
        } else {
            write_gspo_quad(&mut buffer, quad);
            Ok(self.reader.contains_key(&self.storage.gspo_cf, &buffer)?)
        }
    }

    // TODO：方法的含义是啥（在查询的时候用吗，生成迭代?）
    pub fn quads_for_pattern(
        &self,
        subject: Option<&EncodedTerm>,
        predicate: Option<&EncodedTerm>,
        object: Option<&EncodedTerm>,
        graph_name: Option<&EncodedTerm>,
    ) -> ChainedDecodingQuadIterator {
        match subject {    // 先匹配s，再p，再o，再g（这四个EncodedTerm都有可能是空的）
            Some(subject) => match predicate {
                Some(predicate) => match object {
                    Some(object) => match graph_name {
                        Some(graph_name) => self.quads_for_subject_predicate_object_graph( // spog
                            subject, predicate, object, graph_name,
                        ),
                        None => self.quads_for_subject_predicate_object(subject, predicate, object),  // spo
                    },
                    None => match graph_name {
                        Some(graph_name) => {
                            self.quads_for_subject_predicate_graph(subject, predicate, graph_name) // spg
                        }
                        None => self.quads_for_subject_predicate(subject, predicate),   // sp
                    },
                },
                None => match object {
                    Some(object) => match graph_name {
                        Some(graph_name) => {
                            self.quads_for_subject_object_graph(subject, object, graph_name)
                        }
                        None => self.quads_for_subject_object(subject, object),
                    },
                    None => match graph_name {
                        Some(graph_name) => self.quads_for_subject_graph(subject, graph_name),
                        None => self.quads_for_subject(subject),
                    },
                },
            },
            None => match predicate {
                Some(predicate) => match object {
                    Some(object) => match graph_name {
                        Some(graph_name) => {
                            self.quads_for_predicate_object_graph(predicate, object, graph_name)
                        }
                        None => self.quads_for_predicate_object(predicate, object),
                    },
                    None => match graph_name {
                        Some(graph_name) => self.quads_for_predicate_graph(predicate, graph_name),
                        None => self.quads_for_predicate(predicate),     // TODO：s o g是空的
                    },
                },
                None => match object {
                    Some(object) => match graph_name {
                        Some(graph_name) => self.quads_for_object_graph(object, graph_name),
                        None => self.quads_for_object(object),
                    },
                    None => match graph_name {
                        Some(graph_name) => self.quads_for_graph(graph_name),
                        None => self.quads(),
                    },
                },
            },
        }
    }

    // 针对所有的元组
    // 下面的方法应该是给定 s p o g 其中的零个或多个创建迭代器
    // 使用 pair 方法创建，对dspo、gspo分别创建一个迭代器
    pub fn quads(&self) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(self.dspo_quads(&[]), self.gspo_quads(&[]))
    }

    fn quads_in_named_graph(&self) -> DecodingQuadIterator {
        self.gspo_quads(&[])
    }

    // 下面的方法是在九个存储三元组、四元组的表中，给定匹配的模式查询（参照quads_for_pattern方法）
    // 都是使用pair方法创建
    fn quads_for_subject(&self, subject: &EncodedTerm) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dspo_quads(&encode_term(subject)),
            self.spog_quads(&encode_term(subject)),
        )
    }

    fn quads_for_subject_predicate(
        &self,
        subject: &EncodedTerm,
        predicate: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dspo_quads(&encode_term_pair(subject, predicate)),
            self.spog_quads(&encode_term_pair(subject, predicate)),
        )
    }

    fn quads_for_subject_predicate_object(
        &self,
        subject: &EncodedTerm,
        predicate: &EncodedTerm,
        object: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dspo_quads(&encode_term_triple(subject, predicate, object)),
            self.spog_quads(&encode_term_triple(subject, predicate, object)),
        )
    }

    fn quads_for_subject_object(
        &self,
        subject: &EncodedTerm,
        object: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dosp_quads(&encode_term_pair(object, subject)),
            self.ospg_quads(&encode_term_pair(object, subject)),
        )
    }

    // TODO：这个方法有用
    fn quads_for_predicate(&self, predicate: &EncodedTerm) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dpos_quads(&encode_term(predicate)),
            self.posg_quads(&encode_term(predicate)),
        )
    }

    fn quads_for_predicate_object(
        &self,
        predicate: &EncodedTerm,
        object: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dpos_quads(&encode_term_pair(predicate, object)),
            self.posg_quads(&encode_term_pair(predicate, object)),
        )
    }

    fn quads_for_object(&self, object: &EncodedTerm) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::pair(
            self.dosp_quads(&encode_term(object)),
            self.ospg_quads(&encode_term(object)),
        )
    }

    // 加上图之后创建的 ChainedDecodingQuadIterator 就不一样了（使用new方法）
    // 给点图，返回该图上所有元组的迭代器
    fn quads_for_graph(&self, graph_name: &EncodedTerm) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dspo_quads(&Vec::default())
        } else {
            self.gspo_quads(&encode_term(graph_name))
        })
    }

    fn quads_for_subject_graph(
        &self,
        subject: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dspo_quads(&encode_term(subject))
        } else {
            self.gspo_quads(&encode_term_pair(graph_name, subject))
        })
    }

    fn quads_for_subject_predicate_graph(
        &self,
        subject: &EncodedTerm,
        predicate: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dspo_quads(&encode_term_pair(subject, predicate))
        } else {
            self.gspo_quads(&encode_term_triple(graph_name, subject, predicate))
        })
    }

    fn quads_for_subject_predicate_object_graph(
        &self,
        subject: &EncodedTerm,
        predicate: &EncodedTerm,
        object: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {  // 如果是默认图
            self.dspo_quads(&encode_term_triple(subject, predicate, object))   // 传入dspo_quads()的是包含spo的buffer编码字节序列
        } else {
            self.gspo_quads(&encode_term_quad(graph_name, subject, predicate, object))
        })
    }

    fn quads_for_subject_object_graph(
        &self,
        subject: &EncodedTerm,
        object: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dosp_quads(&encode_term_pair(object, subject))
        } else {
            self.gosp_quads(&encode_term_triple(graph_name, object, subject))
        })
    }

    fn quads_for_predicate_graph(
        &self,
        predicate: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dpos_quads(&encode_term(predicate))
        } else {
            self.gpos_quads(&encode_term_pair(graph_name, predicate))
        })
    }

    fn quads_for_predicate_object_graph(
        &self,
        predicate: &EncodedTerm,
        object: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dpos_quads(&encode_term_pair(predicate, object))
        } else {
            self.gpos_quads(&encode_term_triple(graph_name, predicate, object))
        })
    }

    fn quads_for_object_graph(
        &self,
        object: &EncodedTerm,
        graph_name: &EncodedTerm,
    ) -> ChainedDecodingQuadIterator {
        ChainedDecodingQuadIterator::new(if graph_name.is_default_graph() {
            self.dosp_quads(&encode_term(object))
        } else {
            self.gosp_quads(&encode_term_pair(graph_name, object))
        })
    }

    pub fn named_graphs(&self) -> DecodingGraphIterator {
        DecodingGraphIterator {
            iter: self.reader.iter(&self.storage.graphs_cf).unwrap(), //TODO: propagate error?
        }
    }

    pub fn contains_named_graph(&self, graph_name: &EncodedTerm) -> Result<bool, StorageError> {
        self.reader
            .contains_key(&self.storage.graphs_cf, &encode_term(graph_name))
    }



    // 调用self.inner_quads，生成迭代器，在 validate方法里会调用到
    fn spog_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.spog_cf, prefix, QuadEncoding::Spog)
    }

    fn posg_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.posg_cf, prefix, QuadEncoding::Posg)
    }

    fn ospg_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.ospg_cf, prefix, QuadEncoding::Ospg)
    }

    fn gspo_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.gspo_cf, prefix, QuadEncoding::Gspo)
    }

    fn gpos_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.gpos_cf, prefix, QuadEncoding::Gpos)
    }

    fn gosp_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.gosp_cf, prefix, QuadEncoding::Gosp)
    }

    fn dspo_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {    // prefix 实际上就是包含s p o的buffer编码字节序列
        self.inner_quads(&self.storage.dspo_cf, prefix, QuadEncoding::Dspo)
    }

    fn dpos_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.dpos_cf, prefix, QuadEncoding::Dpos)
    }

    fn dosp_quads(&self, prefix: &[u8]) -> DecodingQuadIterator {
        self.inner_quads(&self.storage.dosp_cf, prefix, QuadEncoding::Dosp)
    }

    fn inner_quads(
        &self,
        column_family: &ColumnFamily,
        prefix: &[u8],   // spog的字节编码序列buffer（不定顺序）
        encoding: QuadEncoding,
    ) -> DecodingQuadIterator {
        DecodingQuadIterator {
            iter: self.reader.scan_prefix(column_family, prefix).unwrap(), // TODO: propagate error?
            encoding,
        }
    }

    // 根据 StrHash 编码获得其对应存储的字符串
    #[cfg(not(target_arch = "wasm32"))]
    pub fn get_str(&self, key: &StrHash) -> Result<Option<String>, StorageError> {
        Ok(self
            .storage
            .db
            .get(&self.storage.id2str_cf, &key.to_be_bytes())?
            .map(|v| String::from_utf8(v.into()))
            .transpose()
            .map_err(CorruptionError::new)?)
    }

    #[cfg(target_arch = "wasm32")]
    pub fn get_str(&self, key: &StrHash) -> Result<Option<String>, StorageError> {
        Ok(self
            .reader
            .get(&self.storage.id2str_cf, &key.to_be_bytes())?
            .map(|v| String::from_utf8(v.into()))
            .transpose()
            .map_err(CorruptionError::new)?)
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub fn contains_str(&self, key: &StrHash) -> Result<bool, StorageError> {
        self.storage
            .db
            .contains_key(&self.storage.id2str_cf, &key.to_be_bytes())
    }

    #[cfg(target_arch = "wasm32")]
    pub fn contains_str(&self, key: &StrHash) -> Result<bool, StorageError> {
        self.reader
            .contains_key(&self.storage.id2str_cf, &key.to_be_bytes())
    }

    /// Validates that all the storage invariants held in the data
    // 验证存储的数据是否一致（spo、pos、osp中的元组数量是否一致，四元组也同样）
    #[cfg(not(target_arch = "wasm32"))]
    pub fn validate(&self) -> Result<(), StorageError> {
        // triples
        let dspo_size = self.dspo_quads(&[]).count();
        if dspo_size != self.dpos_quads(&[]).count() || dspo_size != self.dosp_quads(&[]).count() {
            return Err(CorruptionError::new(
                "Not the same number of triples in dspo, dpos and dosp",
            )
            .into());
        }
        for spo in self.dspo_quads(&[]) {
            let spo = spo?;
            self.decode_quad(&spo)?; // We ensure that the quad is readable
            if !self.storage.db.contains_key(
                &self.storage.dpos_cf,
                &encode_term_triple(&spo.predicate, &spo.object, &spo.subject),
            )? {
                return Err(CorruptionError::new("Quad in dspo and not in dpos").into());
            }
            if !self.storage.db.contains_key(
                &self.storage.dosp_cf,
                &encode_term_triple(&spo.object, &spo.subject, &spo.predicate),
            )? {
                return Err(CorruptionError::new("Quad in dspo and not in dpos").into());
            }
        }

        // quads
        let gspo_size = self.gspo_quads(&[]).count();
        if gspo_size != self.gpos_quads(&[]).count()
            || gspo_size != self.gosp_quads(&[]).count()
            || gspo_size != self.spog_quads(&[]).count()
            || gspo_size != self.posg_quads(&[]).count()
            || gspo_size != self.ospg_quads(&[]).count()
        {
            return Err(CorruptionError::new(
                "Not the same number of triples in dspo, dpos and dosp",
            )
            .into());
        }
        for gspo in self.gspo_quads(&[]) {
            let gspo = gspo?;
            self.decode_quad(&gspo)?; // We ensure that the quad is readable
            if !self.storage.db.contains_key(
                &self.storage.gpos_cf,
                &encode_term_quad(
                    &gspo.graph_name,
                    &gspo.predicate,
                    &gspo.object,
                    &gspo.subject,
                ),
            )? {
                return Err(CorruptionError::new("Quad in gspo and not in gpos").into());
            }
            if !self.storage.db.contains_key(
                &self.storage.gosp_cf,
                &encode_term_quad(
                    &gspo.graph_name,
                    &gspo.object,
                    &gspo.subject,
                    &gspo.predicate,
                ),
            )? {
                return Err(CorruptionError::new("Quad in gspo and not in gosp").into());
            }
            if !self.storage.db.contains_key(
                &self.storage.spog_cf,
                &encode_term_quad(
                    &gspo.subject,
                    &gspo.predicate,
                    &gspo.object,
                    &gspo.graph_name,
                ),
            )? {
                return Err(CorruptionError::new("Quad in gspo and not in spog").into());
            }
            if !self.storage.db.contains_key(
                &self.storage.posg_cf,
                &encode_term_quad(
                    &gspo.predicate,
                    &gspo.object,
                    &gspo.subject,
                    &gspo.graph_name,
                ),
            )? {
                return Err(CorruptionError::new("Quad in gspo and not in posg").into());
            }
            if !self.storage.db.contains_key(
                &self.storage.ospg_cf,
                &encode_term_quad(
                    &gspo.object,
                    &gspo.subject,
                    &gspo.predicate,
                    &gspo.graph_name,
                ),
            )? {
                return Err(CorruptionError::new("Quad in gspo and not in ospg").into());
            }
            if !self
                .storage
                .db
                .contains_key(&self.storage.graphs_cf, &encode_term(&gspo.graph_name))?
            {
                return Err(
                    CorruptionError::new("Quad graph name in gspo and not in graphs").into(),
                );
            }
        }
        Ok(())
    }
}


// ##########################################################################
// 在查询时若没有指定图，则使用 pair()新建 dspo、gspo两个迭代器
// 若指定了图，则只使用 new()新建对应图上的迭代器
#[derive(Clone)]
pub struct ChainedDecodingQuadIterator {
    first: DecodingQuadIterator,
    second: Option<DecodingQuadIterator>,
}


impl ChainedDecodingQuadIterator {
    fn new(first: DecodingQuadIterator) -> Self {
        Self {
            first,
            second: None,
        }
    }

    fn pair(first: DecodingQuadIterator, second: DecodingQuadIterator) -> Self {
        Self {
            first,
            second: Some(second),
        }
    }
}

impl Iterator for ChainedDecodingQuadIterator {
    type Item = Result<EncodedQuad, StorageError>; // 被迭代的元素类型

    fn next(&mut self) -> Option<Result<EncodedQuad, StorageError>> {   // 推进迭代器并返回下一个值
        if let Some(result) = self.first.next() {
            Some(result)
        } else if let Some(second) = self.second.as_mut() {
            second.next()
        } else {
            None
        }
    }
}

// ----------------------------------------------------------
#[derive(Clone)]
pub struct DecodingQuadIterator {
    iter: Iter,
    encoding: QuadEncoding,   // 三元组和四元组的九种序列（gspo...）枚举
}

impl Iterator for DecodingQuadIterator {
    type Item = Result<EncodedQuad, StorageError>;

    fn next(&mut self) -> Option<Result<EncodedQuad, StorageError>> {   // 推进迭代器并返回下一个值
        if let Err(e) = self.iter.status() {
            return Some(Err(e));
        }
        let term = self.encoding.decode(self.iter.key()?);
        self.iter.next();
        Some(term)
    }
}

pub struct DecodingGraphIterator {
    iter: Iter,
}

impl Iterator for DecodingGraphIterator {
    type Item = Result<EncodedTerm, StorageError>;   // 进行迭代的元素

    fn next(&mut self) -> Option<Result<EncodedTerm, StorageError>> {
        if let Err(e) = self.iter.status() {
            return Some(Err(e));
        }
        let term = decode_term(self.iter.key()?);   // 将内存里的 buffer 解码成 EncodedTerm
        self.iter.next();
        Some(term)
    }
}

impl StrLookup for StorageReader {
    fn get_str(&self, key: &StrHash) -> Result<Option<String>, StorageError> {
        self.get_str(key)
    }

    fn contains_str(&self, key: &StrHash) -> Result<bool, StorageError> {
        self.contains_str(key)
    }
}

pub struct StorageWriter<'a> {
    buffer: Vec<u8>,
    transaction: Transaction<'a>,
    storage: &'a Storage,
}

impl<'a> StorageWriter<'a> {
    pub fn reader(&self) -> StorageReader {
        StorageReader {
            reader: self.transaction.reader(),
            storage: self.storage.clone(),
        }
    }

    // 重点看了一下insert方法
    // 元组插入使用的是 Transaction 里的insert方法
    // 而Term的插入使用的是Db中的插入方法
    pub fn insert(&mut self, quad: QuadRef<'_>) -> Result<bool, StorageError> {
        let encoded = quad.into();   // type: EncodedQuad
        self.buffer.clear();

        let result = if quad.graph_name.is_default_graph() {    // 如果是写入default graph，则只要spo pos osp
            write_spo_quad(&mut self.buffer, &encoded);    // 使用 EcodedQuad 才能进行字节序列的编码以及写入buffer
            if self.transaction
                .contains_key_for_update(&self.storage.dspo_cf, &self.buffer)?  // 如果之前包含这个三元组，则进行更新，当得到的是false时，说明是新插入的元组
            {
                false
            } else {
                self.transaction
                    .insert_empty(&self.storage.dspo_cf, &self.buffer)?;  // 一个 buffer 绑定到一个列族

                self.buffer.clear();
                write_pos_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.dpos_cf, &self.buffer)?;

                self.buffer.clear();
                write_osp_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.dosp_cf, &self.buffer)?;
                // 以上的代码是在对应的cf上插入 spo（或者其它顺序的）buffer 字节序列

                self.insert_term(quad.subject.into(), &encoded.subject)?;   // TermRef   EncodedTerm
                self.insert_term(quad.predicate.into(), &encoded.predicate)?;
                self.insert_term(quad.object, &encoded.object)?;
                true
            }
        } else {
            write_spog_quad(&mut self.buffer, &encoded);

            if self.transaction
                .contains_key_for_update(&self.storage.spog_cf, &self.buffer)?
            {
                false
            } else {
                self.transaction
                    .insert_empty(&self.storage.spog_cf, &self.buffer)?;

                self.buffer.clear();
                write_posg_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.posg_cf, &self.buffer)?;

                self.buffer.clear();
                write_ospg_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.ospg_cf, &self.buffer)?;

                self.buffer.clear();
                write_gspo_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.gspo_cf, &self.buffer)?;

                self.buffer.clear();
                write_gpos_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.gpos_cf, &self.buffer)?;

                self.buffer.clear();
                write_gosp_quad(&mut self.buffer, &encoded);
                self.transaction
                    .insert_empty(&self.storage.gosp_cf, &self.buffer)?;

                self.insert_term(quad.subject.into(), &encoded.subject)?;
                self.insert_term(quad.predicate.into(), &encoded.predicate)?;
                self.insert_term(quad.object, &encoded.object)?;

                // 开始插入graphTerm
                self.buffer.clear();
                write_term(&mut self.buffer, &encoded.graph_name);
                if !self
                    .transaction
                    .contains_key_for_update(&self.storage.graphs_cf, &self.buffer)?
                {
                    self.transaction
                        .insert_empty(&self.storage.graphs_cf, &self.buffer)?;   // 在graph的cf中插入，只有键没有值
                    self.insert_graph_name(quad.graph_name, &encoded.graph_name)?;// 在id2str中插入
                }
                true
            }
        };
        Ok(result)
    }

    // 闭包可以捕获上下文中的值，insert_term方法中第三个参数是一个闭包，包括两个参数、一行闭包体
    // 当以闭包作为输入参数时，必须指出闭包的完整类型，它是通过使用这三种 trait中的一种来指定的：Fn、FnMut、FnOnce
    // 闭包可以作为参数传递过去，向 numeric_encoder.rs 文件的 insert_term方法传递闭包，并捕获从其中获得的参数值，接着调用闭包，执行闭包体
    fn insert_term(
        &mut self,
        term: TermRef<'_>,
        encoded: &EncodedTerm,
    ) -> Result<(), StorageError> {
        insert_term(term, encoded, &mut |key, value| self.insert_str(key, value))
    }

    // 统一会调用 Db 中的insert方法，往 id2str 中插入
    // SmallString不会往id2str中存
    #[cfg(not(target_arch = "wasm32"))]
    fn insert_str(&mut self, key: &StrHash, value: &str) -> Result<(), StorageError> {
        if self
            .storage
            .db
            .contains_key(&self.storage.id2str_cf, &key.to_be_bytes())?
        {
            return Ok(());
        }
        self.storage.db.insert(
            &self.storage.id2str_cf,
            &key.to_be_bytes(),  // 字节序列,StrHash里只包含一个u128类型的成员
            value.as_bytes(),  // 字节序列
        )
    }

    #[cfg(target_arch = "wasm32")]
    fn insert_str(&mut self, key: &StrHash, value: &str) -> Result<(), StorageError> {
        self.transaction.insert(
            &self.storage.id2str_cf,
            &key.to_be_bytes(),
            value.as_bytes(),
        )
    }

    // TODO：这两个方法有什么不同
    // 对 graph 进行插入
    // 在 is2str上会插入
    // graph的cf上也插入
    pub fn insert_named_graph(
        &mut self,
        graph_name: NamedOrBlankNodeRef<'_>,
    ) -> Result<bool, StorageError> {
        let encoded_graph_name = graph_name.into(); // EnodedTerm

        self.buffer.clear();
        write_term(&mut self.buffer, &encoded_graph_name);

        let result = if self.transaction
            .contains_key_for_update(&self.storage.graphs_cf, &self.buffer)?
        {
            false
        } else {
            self.transaction
                .insert_empty(&self.storage.graphs_cf, &self.buffer)?;
            self.insert_term(graph_name.into(), &encoded_graph_name)?;
            true
        };
        Ok(result)
    }

    // 将 graph的名字进行StrHash编码后在id2str上插入
    // 使用的是Db中的插入方法
    fn insert_graph_name(
        &mut self,
        graph_name: GraphNameRef<'_>,
        encoded: &EncodedTerm,
    ) -> Result<(), StorageError> {
        match graph_name {
            GraphNameRef::NamedNode(graph_name) => self.insert_term(graph_name.into(), encoded),
            GraphNameRef::BlankNode(graph_name) => self.insert_term(graph_name.into(), encoded),
            GraphNameRef::DefaultGraph => Ok(()),
        }
    }


    // 移除三元组（四元组）
    pub fn remove(&mut self, quad: QuadRef<'_>) -> Result<bool, StorageError> {
        self.remove_encoded(&quad.into())
    }

    // id2str上的term并未被删除；以及删除图时，图的str编码也未被删除
    fn remove_encoded(&mut self, quad: &EncodedQuad) -> Result<bool, StorageError> {
        self.buffer.clear();

        let result = if quad.graph_name.is_default_graph() {
            write_spo_quad(&mut self.buffer, quad);

            if self.transaction
                .contains_key_for_update(&self.storage.dspo_cf, &self.buffer)?
            {   // 存在之前的元组
                self.transaction
                    .remove(&self.storage.dspo_cf, &self.buffer)?;

                self.buffer.clear();
                write_pos_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.dpos_cf, &self.buffer)?;

                self.buffer.clear();
                write_osp_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.dosp_cf, &self.buffer)?;
                true
            } else {
                false
            }
        } else {
            write_spog_quad(&mut self.buffer, quad);

            if self
                .transaction
                .contains_key_for_update(&self.storage.spog_cf, &self.buffer)?
            {
                self.transaction
                    .remove(&self.storage.spog_cf, &self.buffer)?;

                self.buffer.clear();
                write_posg_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.posg_cf, &self.buffer)?;

                self.buffer.clear();
                write_ospg_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.ospg_cf, &self.buffer)?;

                self.buffer.clear();
                write_gspo_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.gspo_cf, &self.buffer)?;

                self.buffer.clear();
                write_gpos_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.gpos_cf, &self.buffer)?;

                self.buffer.clear();
                write_gosp_quad(&mut self.buffer, quad);
                self.transaction
                    .remove(&self.storage.gosp_cf, &self.buffer)?;
                true
            } else {
                false
            }
        };
        Ok(result)
    }

    // 删除某一个图（即图上的元组）
    pub fn clear_graph(&mut self, graph_name: GraphNameRef<'_>) -> Result<(), StorageError> {
        if graph_name.is_default_graph() {
            for quad in self.reader().quads_for_graph(&EncodedTerm::DefaultGraph) {
                self.remove_encoded(&quad?)?;
            }
        } else {
            self.buffer.clear();
            write_term(&mut self.buffer, &graph_name.into());
            if self.transaction
                .contains_key_for_update(&self.storage.graphs_cf, &self.buffer)?
            {
                // The condition is useful to lock the graph itself and ensure no quad is inserted at the same time
                for quad in self.reader().quads_for_graph(&graph_name.into()) {
                    self.remove_encoded(&quad?)?;
                }
            }
        }
        Ok(())
    }

    // 清除所有 named_graph（即图上的元组）
    pub fn clear_all_named_graphs(&mut self) -> Result<(), StorageError> {
        for quad in self.reader().quads_in_named_graph() {
            self.remove_encoded(&quad?)?;
        }
        Ok(())
    }

    // 清除所有graph（即图上的元组）
    pub fn clear_all_graphs(&mut self) -> Result<(), StorageError> {
        for quad in self.reader().quads() {
            self.remove_encoded(&quad?)?;
        }
        Ok(())
    }

    // 不仅删除图上的三元组，也将图在 graph_cf 上清除
    pub fn remove_named_graph(
        &mut self,
        graph_name: NamedOrBlankNodeRef<'_>,
    ) -> Result<bool, StorageError> {
        self.remove_encoded_named_graph(&graph_name.into())
    }

    // 移除给定的 named_graph
    // 不仅删除图上的三元组，也将图在 graph_cf 上清除
    fn remove_encoded_named_graph(
        &mut self,
        graph_name: &EncodedTerm,
    ) -> Result<bool, StorageError> {
        self.buffer.clear();
        write_term(&mut self.buffer, graph_name);

        let result = if self
            .transaction
            .contains_key_for_update(&self.storage.graphs_cf, &self.buffer)?
        {
            // The condition is done ASAP to lock the graph itself
            for quad in self.reader().quads_for_graph(graph_name) {
                self.remove_encoded(&quad?)?;
            }
            self.buffer.clear();
            write_term(&mut self.buffer, graph_name);
            self.transaction
                .remove(&self.storage.graphs_cf, &self.buffer)?;
            true
        } else {
            false
        };
        Ok(result)
    }

    // 移除所有的 named_graph
    // 不仅删除图上的三元组，也将图在 graph_cf 上清除
    pub fn remove_all_named_graphs(&mut self) -> Result<(), StorageError> {
        for graph_name in self.reader().named_graphs() {
            self.remove_encoded_named_graph(&graph_name?)?;
        }
        Ok(())
    }

    // 清除所有元组（包括默认图以及命名图）
    // 并清除 graph_cf
    pub fn clear(&mut self) -> Result<(), StorageError> {
        for graph_name in self.reader().named_graphs() {
            self.remove_encoded_named_graph(&graph_name?)?;
        }
        for quad in self.reader().quads() {
            self.remove_encoded(&quad?)?;
        }
        Ok(())
    }
}


// 在 store.rs 中用到了
#[cfg(not(target_arch = "wasm32"))]
pub struct StorageBulkLoader {
    storage: Storage,
    hooks: Vec<Box<dyn Fn(u64)>>,
    num_threads: Option<usize>,
    max_memory_size: Option<usize>,
}

#[cfg(not(target_arch = "wasm32"))]
impl StorageBulkLoader {
    pub fn new(storage: Storage) -> Self {
        Self {
            storage,
            hooks: Vec::new(),
            num_threads: None,
            max_memory_size: None,
        }
    }

    pub fn set_num_threads(mut self, num_threads: usize) -> Self {
        self.num_threads = Some(num_threads);
        self
    }

    pub fn set_max_memory_size_in_megabytes(mut self, max_memory_size: usize) -> Self {
        self.max_memory_size = Some(max_memory_size);
        self
    }

    pub fn on_progress(mut self, callback: impl Fn(u64) + 'static) -> Self {
        self.hooks.push(Box::new(callback));
        self
    }

    // 注意一下，这个方法也重写了
    pub fn load<EI, EO: From<StorageError> + From<EI>, I: IntoIterator<Item = Result<Quad, EI>>>(
        &self,
        quads: I,
    ) -> Result<(), EO> {
        let system = System::new_all();
        let cpu_count = min(4, system.physical_core_count().unwrap_or(2));
        let num_threads = max(
            if let Some(num_threads) = self.num_threads {
                num_threads
            } else if let Some(max_memory_size) = self.max_memory_size {
                min(
                    cpu_count,
                    max_memory_size * 1000 / DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            } else {
                cpu_count
            },
            2,
        );
        let batch_size = min(
            if let Some(max_memory_size) = self.max_memory_size {
                max(1000, max_memory_size * 1000 / num_threads)
            } else {
                max(
                    usize::try_from(system.free_memory()).unwrap() / num_threads,
                    DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            },
            MAX_BULK_LOAD_BATCH_SIZE,
        );
        let mut threads = VecDeque::with_capacity(num_threads - 1);
        let mut buffer = Vec::with_capacity(batch_size);
        let done_counter = Arc::new(AtomicU64::new(0));
        let mut done_and_displayed_counter = 0;

        for quad in quads {
            let quad = quad?;
            buffer.push(quad);    // 其中是Quad
            if buffer.len() >= batch_size {
                self.spawn_load_thread(
                    &mut buffer,
                    &mut threads,
                    &done_counter,
                    &mut done_and_displayed_counter,
                    num_threads,
                )?;
            }
        }
        self.spawn_load_thread(
            &mut buffer,
            &mut threads,
            &done_counter,
            &mut done_and_displayed_counter,
            num_threads,
        )?;
        for thread in threads {
            thread.join().unwrap()?;
            self.on_possible_progress(&done_counter, &mut done_and_displayed_counter);
        }
        Ok(())
    }

    fn spawn_load_thread(
        &self,
        buffer: &mut Vec<Quad>,
        threads: &mut VecDeque<JoinHandle<Result<(), StorageError>>>,
        done_counter: &Arc<AtomicU64>,
        done_and_displayed_counter: &mut u64,
        num_threads: usize,
    ) -> Result<(), StorageError> {
        self.on_possible_progress(done_counter, done_and_displayed_counter);
        // We avoid to have too many threads
        if threads.len() >= num_threads {
            if let Some(thread) = threads.pop_front() {
                thread.join().unwrap()?;
                self.on_possible_progress(done_counter, done_and_displayed_counter);
            }
        }
        let buffer = take(buffer);
        let storage = self.storage.clone();
        let done_counter_clone = done_counter.clone();
        threads.push_back(spawn(move || {
            FileBulkLoader::new(storage).load(buffer, &done_counter_clone)   // TODO:这里面有插入的方法了
        }));
        self.on_possible_progress(done_counter, done_and_displayed_counter);
        Ok(())
    }



    // ############################## 将区间编码加入value中 ##############################
    // 重写的方法
    pub fn load_oxiuse_value<EI, EO: From<StorageError> + From<EI>, I: IntoIterator<Item = Result<Quad, EI>>>(
        &self,
        quads: I,
        tree_path:&'static str
    ) -> Result<(), EO> {
        let system = System::new_all();
        let cpu_count = min(4, system.physical_core_count().unwrap_or(2));
        let num_threads = max(
            if let Some(num_threads) = self.num_threads {
                num_threads
            } else if let Some(max_memory_size) = self.max_memory_size {
                min(
                    cpu_count,
                    max_memory_size * 1000 / DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            } else {
                cpu_count
            },
            2,
        );
        let batch_size = min(
            if let Some(max_memory_size) = self.max_memory_size {
                max(1000, max_memory_size * 1000 / num_threads)
            } else {
                max(
                    usize::try_from(system.free_memory()).unwrap() / num_threads,
                    DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            },
            MAX_BULK_LOAD_BATCH_SIZE,
        );
        let mut threads = VecDeque::with_capacity(num_threads - 1);
        let mut buffer = Vec::with_capacity(batch_size);
        let done_counter = Arc::new(AtomicU64::new(0));
        let mut done_and_displayed_counter = 0;

        for quad in quads {
            let quad = quad?;
            buffer.push(quad);    // 其中是Quad
            if buffer.len() >= batch_size {
                self.spawn_load_thread_oxiuse_value(  // TODO：记得修改方法
                    &mut buffer,
                    &mut threads,
                    &done_counter,
                    &mut done_and_displayed_counter,
                    num_threads,
                    tree_path
                )?;
            }
        }
        self.spawn_load_thread_oxiuse_value(    // TODO：记得修改方法
            &mut buffer,
            &mut threads,
            &done_counter,
            &mut done_and_displayed_counter,
            num_threads,
            tree_path
        )?;
        for thread in threads {
            thread.join().unwrap()?;
            self.on_possible_progress(&done_counter, &mut done_and_displayed_counter);
        }
        Ok(())
    }

    // 在这个版本中才加入tree的读取构造
    fn spawn_load_thread_oxiuse_value(
        &self,
        buffer: &mut Vec<Quad>,
        threads: &mut VecDeque<JoinHandle<Result<(), StorageError>>>,
        done_counter: &Arc<AtomicU64>,
        done_and_displayed_counter: &mut u64,
        num_threads: usize,
        tree_path: &'static str
    ) -> Result<(), StorageError> {
        self.on_possible_progress(done_counter, done_and_displayed_counter);
        // We avoid to have too many threads
        if threads.len() >= num_threads {
            if let Some(thread) = threads.pop_front() {
                thread.join().unwrap()?;
                self.on_possible_progress(done_counter, done_and_displayed_counter);
            }
        }

        // 为了在线程之中安全转移，之后传递的是vec
        let buffer = take(buffer);
        let storage = self.storage.clone();
        let done_counter_clone = done_counter.clone();

        // TODO:多线程的问题还没解决
        // 这大概是使用多线程插入数据，速度会加快，move会将所有权丢给线程
        threads.push_back(spawn( move || {
            FileBulkLoader::new(storage).load_oxiuse_value(buffer, &done_counter_clone, tree_path)   // TODO:记得修改方法
        }));

        self.on_possible_progress(done_counter, done_and_displayed_counter);
        Ok(())
    }

    // ############################## 将区间编码加入key中 ##############################
    pub fn load_oxiuse_key<EI, EO: From<StorageError> + From<EI>, I: IntoIterator<Item = Result<Quad, EI>>>(
        &self,
        quads: I,
        tree_path:&'static str
    ) -> Result<(), EO> {
        let system = System::new_all();
        let cpu_count = min(4, system.physical_core_count().unwrap_or(2));
        let num_threads = max(
            if let Some(num_threads) = self.num_threads {
                num_threads
            } else if let Some(max_memory_size) = self.max_memory_size {
                min(
                    cpu_count,
                    max_memory_size * 1000 / DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            } else {
                cpu_count
            },
            2,
        );
        let batch_size = min(
            if let Some(max_memory_size) = self.max_memory_size {
                max(1000, max_memory_size * 1000 / num_threads)
            } else {
                max(
                    usize::try_from(system.free_memory()).unwrap() / num_threads,
                    DEFAULT_BULK_LOAD_BATCH_SIZE,
                )
            },
            MAX_BULK_LOAD_BATCH_SIZE,
        );
        let mut threads = VecDeque::with_capacity(num_threads - 1);
        let mut buffer = Vec::with_capacity(batch_size);
        let done_counter = Arc::new(AtomicU64::new(0));
        let mut done_and_displayed_counter = 0;

        for quad in quads {
            let quad = quad?;
            buffer.push(quad);    // 其中是Quad
            if buffer.len() >= batch_size {
                self.spawn_load_thread_oxiuse_key(  // TODO：记得修改方法
                    &mut buffer,
                    &mut threads,
                    &done_counter,
                    &mut done_and_displayed_counter,
                    num_threads,
                    tree_path
                )?;
            }
        }
        self.spawn_load_thread_oxiuse_key(    // TODO：记得修改方法
            &mut buffer,
            &mut threads,
            &done_counter,
            &mut done_and_displayed_counter,
            num_threads,
            tree_path
        )?;
        for thread in threads {
            thread.join().unwrap()?;
            self.on_possible_progress(&done_counter, &mut done_and_displayed_counter);
        }
        Ok(())
    }

    // 在这个版本中才加入tree的读取构造
    fn spawn_load_thread_oxiuse_key(
        &self,
        buffer: &mut Vec<Quad>,
        threads: &mut VecDeque<JoinHandle<Result<(), StorageError>>>,
        done_counter: &Arc<AtomicU64>,
        done_and_displayed_counter: &mut u64,
        num_threads: usize,
        tree_path: &'static str
    ) -> Result<(), StorageError> {
        self.on_possible_progress(done_counter, done_and_displayed_counter);
        // We avoid to have too many threads
        if threads.len() >= num_threads {
            if let Some(thread) = threads.pop_front() {
                thread.join().unwrap()?;
                self.on_possible_progress(done_counter, done_and_displayed_counter);
            }
        }

        // 为了在线程之中安全转移，之后传递的是vec
        let buffer = take(buffer);
        let storage = self.storage.clone();
        let done_counter_clone = done_counter.clone();

        // TODO:多线程的问题还没解决
        // 这大概是使用多线程插入数据，速度会加快，move会将所有权丢给线程
        threads.push_back(spawn( move || {
            FileBulkLoader::new(storage).load_oxiuse_key(buffer, &done_counter_clone, tree_path)   // TODO:记得修改方法
        }));

        self.on_possible_progress(done_counter, done_and_displayed_counter);
        Ok(())
    }


    fn on_possible_progress(&self, done: &AtomicU64, done_and_displayed: &mut u64) {
        let new_counter = done.fetch_max(*done_and_displayed, Ordering::Relaxed);
        let display_step = u64::try_from(DEFAULT_BULK_LOAD_BATCH_SIZE).unwrap();
        if new_counter % display_step > *done_and_displayed % display_step {
            for hook in &self.hooks {
                hook(new_counter);
            }
        }
        *done_and_displayed = new_counter;
    }
}



#[cfg(not(target_arch = "wasm32"))]
struct FileBulkLoader {
    storage: Storage,
    id2str: HashMap<StrHash, Box<str>>,
    quads: HashSet<EncodedQuad>,
    triples: HashSet<EncodedQuad>,
    graphs: HashSet<EncodedTerm>,
}

#[cfg(not(target_arch = "wasm32"))]
impl FileBulkLoader {
    fn new(storage: Storage) -> Self {
        Self {
            storage,
            id2str: HashMap::default(),
            quads: HashSet::default(),
            triples: HashSet::default(),
            graphs: HashSet::default(),
        }
    }

    
    fn load(
        &mut self,
        quads: impl IntoIterator<Item = Quad>,
        counter: &AtomicU64,
        
    ) -> Result<(), StorageError> {
        self.encode(quads)?;   

        let size = self.triples.len() + self.quads.len();

        self.save()?;    
        
        counter.fetch_add(size.try_into().unwrap(), Ordering::Relaxed);
        Ok(())
    }

    // 该方法主要是获得self的id2str hashmap
    fn encode(&mut self, quads: impl IntoIterator<Item = Quad>) -> Result<(), StorageError> {
        for quad in quads {
            let encoded = EncodedQuad::from(quad.as_ref());   // 转成EncodedQuad，由EcodedTerm组成
            if quad.graph_name.is_default_graph() {
                if self.triples.insert(encoded.clone()) {   // 先在自己的triples中插入EncodedQuad，然后将spo传入insert_term方法（不会重复插入）
                    self.insert_term(quad.subject.as_ref().into(), &encoded.subject)?;
                    self.insert_term(quad.predicate.as_ref().into(), &encoded.predicate)?;
                    self.insert_term(quad.object.as_ref(), &encoded.object)?;
                }
            } else if self.quads.insert(encoded.clone()) {
                self.insert_term(quad.subject.as_ref().into(), &encoded.subject)?;
                self.insert_term(quad.predicate.as_ref().into(), &encoded.predicate)?;
                self.insert_term(quad.object.as_ref(), &encoded.object)?;

                if self.graphs.insert(encoded.graph_name.clone()) {
                    self.insert_term(
                        match quad.graph_name.as_ref() {
                            GraphNameRef::NamedNode(n) => n.into(),
                            GraphNameRef::BlankNode(n) => n.into(),
                            GraphNameRef::DefaultGraph => unreachable!(),
                        },
                        &encoded.graph_name,
                    )?;
                }
            }
        }
        Ok(())
    }


    fn save(&mut self) -> Result<(), StorageError> {
        let mut to_load = Vec::new();

        if !self.id2str.is_empty() {
            let mut id2str = take(&mut self.id2str)
                .into_iter()
                .map(|(k, v)| (k.to_be_bytes(), v))
                .collect::<Vec<_>>();
            id2str.sort_unstable();
            let mut id2str_sst = self.storage.db.new_sst_file()?;
            for (k, v) in id2str {
                id2str_sst.insert(&k, v.as_bytes())?;
            }
            to_load.push((&self.storage.id2str_cf, id2str_sst.finish()?));
        }

        if !self.triples.is_empty() {
            to_load.push((
                &self.storage.dspo_cf,
                self.build_sst_for_keys(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {  // 在每个元素上调用该闭包，获取三元组的字节序列，只能返回一个元素
                        encode_term_triple(&quad.subject, &quad.predicate, &quad.object)
                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dpos_cf,
                self.build_sst_for_keys(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {  // 在每个元素上调用该闭包，获取三元组的字节序列，只能返回一个元素
                        encode_term_triple(&quad.predicate, &quad.object, &quad.subject)

                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dosp_cf,
                self.build_sst_for_keys(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {  // 在每个元素上调用该闭包，获取三元组的字节序列，只能返回一个元素
                        encode_term_triple(&quad.object, &quad.subject, &quad.predicate)

                    }),
                )?,
            ));
            self.triples.clear();
        }

        if !self.quads.is_empty() {
            to_load.push((
                &self.storage.graphs_cf,
                self.build_sst_for_keys(self.graphs.iter().map(encode_term))?,
            ));
            self.graphs.clear();

            to_load.push((
                &self.storage.gspo_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gpos_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gosp_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.spog_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.posg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.ospg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                        &quad.graph_name,
                    )
                }))?,
            ));
            self.quads.clear();
        }

        self.storage.db.insert_stt_files(&to_load)
    }

    fn build_sst_for_keys(
        &self,
        values: impl Iterator<Item = Vec<u8>>,
    ) -> Result<PathBuf, StorageError> {
        let mut values = values.collect::<Vec<_>>();
        values.sort_unstable();

        let mut sst = self.storage.db.new_sst_file()?;

        for value in values {  
            sst.insert_empty(&value)?;
        }


        sst.finish()   // 不用看了
    }



    // ############################## 将区间编码加入value中 ##############################
    // 插入在这！！！！！！！！！！！！！
    // 接下来的方法也要重新复制一份形成 oxiuse
    fn load_oxiuse_value(
        &mut self,
        quads: impl IntoIterator<Item = Quad>,
        counter: &AtomicU64,
        path: &str
    ) -> Result<(), StorageError> {
        let trees =self.construct_tree(path).unwrap();

        self.encode(quads)?;   // 该方法主要是获得self的id2str hashmap

        let size = self.triples.len() + self.quads.len();

        self.save_oxiuse_value(trees)?;    // TODO:记得修改方法
        
        counter.fetch_add(size.try_into().unwrap(), Ordering::Relaxed);
        Ok(())
    }



    // 三元组的插入在这个方法中，这个方法不可以公用
    fn save_oxiuse_value(&mut self, trees: (MultiTree, MultiTree)) -> Result<(), StorageError> {
        let mut to_load = Vec::new();

        // id2str
        if !self.id2str.is_empty() {
            let mut id2str = take(&mut self.id2str)
                .into_iter()
                .map(|(k, v)| (k.to_be_bytes(), v))
                .collect::<Vec<_>>();
            id2str.sort_unstable();
            let mut id2str_sst = self.storage.db.new_sst_file()?;
            for (k, v) in id2str {
                id2str_sst.insert(&k, v.as_bytes())?;
            }
            to_load.push((&self.storage.id2str_cf, id2str_sst.finish()?));
        }

        // triple（集中在这里）
        // TODO:考虑写一个新方法将（key，value）作为元组返回代替encode_term_triple()
        if !self.triples.is_empty() {
            to_load.push((
                &self.storage.dspo_cf,
                self.build_sst_for_oxiuse_value(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {  // 在每个元素上调用该闭包，获取三元组的字节序列，只能返回一个元素
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_value_spo(map, trees.clone())   // TODO:记得修改方法
                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dpos_cf,
                self.build_sst_for_oxiuse_value(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_value_pos(map, trees.clone())   // TODO:记得修改方法   
                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dosp_cf,
                self.build_sst_for_oxiuse_value(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_value_osp(map, trees.clone())   // TODO:记得修改方法
                    }),
                )?,
            ));
            self.triples.clear();
        }

        if !self.quads.is_empty() {
            to_load.push((
                &self.storage.graphs_cf,
                self.build_sst_for_keys(self.graphs.iter().map(encode_term))?,
            ));
            self.graphs.clear();

            to_load.push((
                &self.storage.gspo_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gpos_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gosp_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.spog_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.posg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.ospg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                        &quad.graph_name,
                    )
                }))?,
            ));
            self.quads.clear();
        }

        self.storage.db.insert_stt_files(&to_load)
    }


    // TODO：使用insert_key_value()，对key、value进行插入
    fn build_sst_for_oxiuse_value(
        &self,
        values: impl Iterator<Item = (Vec<u8>, Vec<u8>)>,
    ) -> Result<PathBuf, StorageError> {
        let mut values = values.collect::<Vec<_>>();
        values.sort_unstable();

        let mut sst = self.storage.db.new_sst_file()?;

        for value in values {    
            sst.insert_key_value(&value.0, &value.1)?;      // TODO:记得修改方法
        }

        
        sst.finish()
    }


    // ############### 将区间编码加入key中  ###############
    // 插入在这！！！！！！！！！！！！！
    // 接下来的方法也要重新复制一份形成 oxiuse
    fn load_oxiuse_key(
        &mut self,
        quads: impl IntoIterator<Item = Quad>,
        counter: &AtomicU64,
        path: &str
    ) -> Result<(), StorageError> {
        // 构造 tree
        let trees =self.construct_tree(path).unwrap();

        self.encode(quads)?;   // 该方法主要是获得self的id2str hashmap

        let size = self.triples.len() + self.quads.len();

        self.save_oxiuse_key(trees)?;    // TODO:记得修改方法
        
        counter.fetch_add(size.try_into().unwrap(), Ordering::Relaxed);
        Ok(())
    }



    // 三元组的插入在这个方法中，这个方法不可以公用
    fn save_oxiuse_key(&mut self, trees: (MultiTree, MultiTree)) -> Result<(), StorageError> {
        let mut to_load = Vec::new();

        // id2str
        if !self.id2str.is_empty() {
            let mut id2str = take(&mut self.id2str)
                .into_iter()
                .map(|(k, v)| (k.to_be_bytes(), v))
                .collect::<Vec<_>>();
            id2str.sort_unstable();
            let mut id2str_sst = self.storage.db.new_sst_file()?;
            for (k, v) in id2str {
                id2str_sst.insert(&k, v.as_bytes())?;
            }
            to_load.push((&self.storage.id2str_cf, id2str_sst.finish()?));
        }

        // triple（集中在这里）
        // TODO:考虑写一个新方法将（key，value）作为元组返回代替encode_term_triple()
        if !self.triples.is_empty() {
            to_load.push((
                &self.storage.dspo_cf,
                self.build_sst_for_oxiuse_key(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {  // 在每个元素上调用该闭包，获取三元组的字节序列，只能返回一个元素
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_key_spo(map, trees.clone())   // TODO:记得修改方法
                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dpos_cf,
                self.build_sst_for_oxiuse_key(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_key_pos(map, trees.clone())   // TODO:记得修改方法   
                    }),
                )?,
            ));
            to_load.push((
                &self.storage.dosp_cf,
                self.build_sst_for_oxiuse_key(   // TODO:记得修改方法
                    self.triples.iter().map(|quad| {
                        let mut map = HashMap::new();
                        map.insert("s", &quad.subject);
                        map.insert("p", &quad.predicate);
                        map.insert("o", &quad.object);

                        encode_term_triple_oxiuse_key_osp(map, trees.clone())   // TODO:记得修改方法
                    }),
                )?,
            ));
            self.triples.clear();
        }

        if !self.quads.is_empty() {
            to_load.push((
                &self.storage.graphs_cf,
                self.build_sst_for_keys(self.graphs.iter().map(encode_term))?,
            ));
            self.graphs.clear();

            to_load.push((
                &self.storage.gspo_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gpos_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.gosp_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.graph_name,
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.spog_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.subject,
                        &quad.predicate,
                        &quad.object,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.posg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.predicate,
                        &quad.object,
                        &quad.subject,
                        &quad.graph_name,
                    )
                }))?,
            ));
            to_load.push((
                &self.storage.ospg_cf,
                self.build_sst_for_keys(self.quads.iter().map(|quad| {
                    encode_term_quad(
                        &quad.object,
                        &quad.subject,
                        &quad.predicate,
                        &quad.graph_name,
                    )
                }))?,
            ));
            self.quads.clear();
        }

        self.storage.db.insert_stt_files(&to_load)
    }


    // TODO：使用insert_key_value()，对key、value进行插入
    fn build_sst_for_oxiuse_key(
        &self,
        values: impl Iterator<Item = (Vec<u8>)>,
    ) -> Result<PathBuf, StorageError> {
        let mut values = values.collect::<Vec<_>>();
        values.sort_unstable();

        let mut sst = self.storage.db.new_sst_file()?;

        for value in values {    
            sst.insert_empty(&value)?;      // TODO:记得修改方法
        }

        
        sst.finish()
    }




    fn insert_term(   // insert_term将获得NamedNode中的str以及对应的EncodedTerm中的StrHash，插入到自己的id2str hashmap中（这部分应该是不用修改的）
        &mut self,
        term: TermRef<'_>,
        encoded: &EncodedTerm,
    ) -> Result<(), StorageError> {
        insert_term(term, encoded, &mut |key, value| {
            self.id2str.entry(*key).or_insert_with(|| value.into());
            Ok(())
        })
    }



    // 构造Class树和属性树（已更新）
    pub fn construct_tree(&self, path: &str) -> Result<(MultiTree, MultiTree), ()>{
        if let Ok(lines) = self.read_lines(path) {
            let classTree = MultiTree::new(owl::OWL_CLASS);
            let propertyTree = MultiTree::new(rdf::PROPERTY); 
    
            for line in lines {
                if let Ok(triple) = line {
                    let vec:Vec<&str> = triple.split(' ').collect();
    
                    let p = &vec[1][1..vec[1].len()-1];
                    if p == rdfs::SUB_CLASS_OF || p == lubm::SUB_ORGANIZATION{
                        let s = &vec[0][1..vec[0].len()-1];
                        let o = &vec[2][1..vec[2].len()-1];
                        
                        classTree.insert(s, o);
                    } else if p == rdfs::SUB_PROPERTY_OF {
                        let s = &vec[0][1..vec[0].len()-1];
                        let o = &vec[2][1..vec[2].len()-1];
                        
                        propertyTree.insert(s, o);
                    }
                }      
            }   
    
            classTree.encode();
            propertyTree.encode();
    
            return Ok((classTree, propertyTree))
        }
        Err(())
    }

    fn read_lines<P>(&self, filename: P) -> io::Result<io::Lines<io::BufReader<File>>> where P: AsRef<Path>, {
        let file = File::open(filename)?;
        Ok(io::BufReader::new(file).lines())
    }
}
