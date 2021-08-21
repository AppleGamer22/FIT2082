.PHONY: init build ecbs geas lazycbs clean

init:
	sudo apt update
	sudo apt install -y build-essential gcc g++ make ocaml opam libboost-all-dev libsparsehash-dev

build: ecbs geas lazycbs

ecbs:
	cd ECBS_PF && $(MAKE)

geas:
	cd geas && $(MAKE)

lazycbs:
	cd lazycbs && $(MAKE)

clean:
	cd ECBS_PF && $(MAKE) clean
	cd -
	cd geas && $(MAKE) clean
	cd -
	cd lazycbs && $(MAKE) clean
	cd -
