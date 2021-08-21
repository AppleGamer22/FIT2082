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
	cd -
	./lazycbs/lazy-cbs --map maps/warehouse-10-20-10-2-1.map.ecbs --agents scenarios/even/warehouse-10-20-10-2-1-even-1.scen --upto 5

clean:
	cd ECBS_PF && $(MAKE) clean
	cd -
	cd geas && $(MAKE) clean
	cd -
	cd lazycbs && $(MAKE) clean
	cd -
