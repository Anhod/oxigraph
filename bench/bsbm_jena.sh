#!/usr/bin/env bash

DATASET_SIZE=100000 # number of products in the dataset. There is around 350 triples generated by product.
PARALLELISM=16
VERSION="4.3.2"
cd bsbm-tools
./generate -fc -pc ${DATASET_SIZE} -s nt -fn "explore-${DATASET_SIZE}" -ud -ufn "explore-update-${DATASET_SIZE}"
wget https://downloads.apache.org/jena/binaries/apache-jena-${VERSION}.zip
unzip apache-jena-${VERSION}.zip
rm apache-jena-${VERSION}.zip
./apache-jena-${VERSION}/bin/tdb2.tdbloader --loader=parallel --loc=td_data "explore-${DATASET_SIZE}.nt"
wget https://downloads.apache.org/jena/binaries/apache-jena-fuseki-${VERSION}.zip
unzip apache-jena-fuseki-${VERSION}.zip
rm apache-jena-fuseki-${VERSION}.zip
echo "rootLogger.level = ERROR" > ./apache-jena-fuseki-${VERSION}/log4j2.properties
./apache-jena-fuseki-${VERSION}/fuseki-server --tdb2 --loc=td_data --update /bsbm &
sleep 10
./testdriver -mt ${PARALLELISM} -ucf usecases/explore/sparql.txt -o "../bsbm.explore.jena.${VERSION}.${DATASET_SIZE}.${PARALLELISM}.xml" http://localhost:3030/bsbm/query
./testdriver -mt ${PARALLELISM} -ucf usecases/exploreAndUpdate/sparql.txt -o "../bsbm.exploreAndUpdate.jena.${VERSION}.${DATASET_SIZE}.${PARALLELISM}.xml" http://localhost:3030/bsbm/query -u http://localhost:3030/bsbm/update -udataset "explore-update-${DATASET_SIZE}.nt"
#./testdriver -mt ${PARALLELISM} -ucf usecases/businessIntelligence/sparql.txt -o "../bsbm.businessIntelligence.jena.${VERSION}.${DATASET_SIZE}.${PARALLELISM}.xml" http://localhost:3030/bsbm/query
kill $!
rm "explore-${DATASET_SIZE}.nt"
rm "explore-update-${DATASET_SIZE}.nt"
rm -r td_data
rm -r run
rm -r apache-jena-${VERSION}
rm -r apache-jena-fuseki-${VERSION}
