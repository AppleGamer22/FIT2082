.PHONY: init build ecbs geas lazycbs clean

init:
	sudo apt update
	sudo apt install -y build-essential gcc g++ make ocaml opam libboost-all-dev libsparsehash-dev
	opam init
	echo 'eval "$(opam config env)"' >> ~/.bashrc
	source ~/.bashrc
	opam install camlidl

build: ecbs geas lazycbs

ecbs:
	cd ECBS_PF && $(MAKE)

geas:
	cd geas && $(MAKE)

lazycbs:
	cd lazycbs && $(MAKE)
	cd -
	echo "warehouse-10-20-10-2-1 with 10 agents"
	./lazycbs/lazy-cbs --map maps/warehouse-10-20-10-2-1.map.ecbs --agents scenarios/even/warehouse-10-20-10-2-1-even-1.scen --upto 40

clean:
	cd ECBS_PF && $(MAKE) clean
	cd -
	cd geas && $(MAKE) clean
	cd -
	cd lazycbs && $(MAKE) clean
	cd -
