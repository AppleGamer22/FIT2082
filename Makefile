.PHONY: init build ecbs geas lazycbs clean

SHELL := /bin/bash

init:
	touch ~/.hushlogin
	sudo apt update
	sudo apt install -y build-essential gcc g++ make ocaml opam libboost-all-dev libsparsehash-dev python-dev pybind11-dev python3-pybind11
	opam init
	echo 'eval "$$(opam config env)"' >> ~/.bashrc
	opam install camlidl
	source ~/.bashrc

build: ecbs geas lazycbs

ecbs:
	cd ECBS_PF && $(MAKE)

geas:
	cd geas && $(MAKE)

lazycbs:
	cd lazycbs && $(MAKE)
	cd -
	./lazycbs/lazy-cbs --map maps/debug-6-6.map.ecbs --agents scenarios/debug-6-6-2-2.scen --upto 2

clean:
	cd ECBS_PF && $(MAKE) clean
	cd -
	cd geas && $(MAKE) clean
	cd -
	cd lazycbs && $(MAKE) clean
	cd -
