#!/bin/bash
touch /home/vagrant/.hushlogin
sudo apt update
sudo apt install -y build-essential gcc g++ make ocaml opam git libboost-all-dev libsparsehash-dev
opam init
eval "$(opam config env)"
opam install camlidl
cd /home/vagrant
git clone https://AppleGamer22@bitbucket.org/gkgange/geas.git
cd geas
make
cd ..
curl -L https://bitbucket.org/gkgange/lazycbs/downloads/ECBS_PF.tar.gz > ECBS_PF.tar.gz
tar -xvzf ECBS_PF.tar.gz
cd ECBS_PF
make
cd ../lazycbs
make