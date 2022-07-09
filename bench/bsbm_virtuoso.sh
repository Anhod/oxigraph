#!/usr/bin/env bash

DATASET_SIZE=100000 # number of products in the dataset. There is around 350 triples generated by product.
PARALLELISM=16
VERSION="7.2.5"
cd bsbm-tools
./generate -fc -pc ${DATASET_SIZE} -s nt -fn "explore-${DATASET_SIZE}" -ud -ufn "explore-update-${DATASET_SIZE}"
cp ../virtuoso-opensource/database/virtuoso.ini.sample virtuoso.ini
mkdir ../database
../virtuoso-opensource/bin/virtuoso-t -f &
sleep 10
../virtuoso-opensource/bin/isql 1111 dba dba <<EOF
SPARQL CREATE GRAPH <urn:graph:test>;
ld_dir('$(realpath .)', 'explore-${DATASET_SIZE}.nt', 'urn:graph:test');
rdf_loader_run();
EOF
./testdriver -mt ${PARALLELISM} -ucf usecases/explore/sparql.txt -o "../bsbm.explore.virtuoso.${VERSION}.${DATASET_SIZE}.${PARALLELISM}.xml" 'http://localhost:8890/sparql?graph-uri=urn:graph:test'
# ./testdriver -mt ${PARALLELISM} -ucf usecases/exploreAndUpdate/sparql.txt -o "../bsbm.exploreAndUpdate.virtuoso.${DATASET_SIZE}.${PARALLELISM}.${PARALLELISM}.${VERSION}.xml" 'http://localhost:8890/sparql?graph-uri=urn:graph:test' -u 'http://dba:dba@localhost:8890/sparql-auth?graph-uri=urn:graph:test' -udataset "explore-update-${DATASET_SIZE}.nt"
# ./testdriver -mt ${PARALLELISM} -ucf usecases/businessIntelligence/sparql.txt -o "../bsbm.businessIntelligence.virtuoso.${VERSION}.${DATASET_SIZE}.${PARALLELISM}.xml" 'http://localhost:8890/sparql?graph-uri=urn:graph:test'
kill $!
rm -r ../database
rm "explore-${DATASET_SIZE}.nt"
rm "explore-update-${DATASET_SIZE}.nt"
rm -r td_data
