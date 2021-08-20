Vagrant.configure("2") do |config|
	config.ssh.insert_key = false
	config.vm.provider "virtualbox" do |virtualbox|
		virtualbox.memory = 2048
		virtualbox.cpus = 2
		virtualbox.gui = false
		virtualbox.name = "FIT2082"
	end
	config.vm.box = "ubuntu/focal64"
	config.vm.hostname = "ubuntu"
	config.vm.synced_folder ".", "/home/vagrant/Documents/FIT2082", create: true
	# config.trigger.after :"Vagrant::Action::Builtin::SyncedFolders" do |t|
	# 	config.vm.provision "shell", privileged: false, inline: <<-SCRIPT
	# 		touch /home/vagrant/.hushlogin
	# 		sudo apt update && sudo apt upgrade -y
	# 		sudo apt install -y build-essential gcc g++ make ocaml opam git libboost-all-dev libsparsehash-dev
	# 		opam init
	# 		eval "$(opam config env)"
	# 		opam install camlidl
	# 		cd /home/vagrant
	# 		git clone https://AppleGamer22@bitbucket.org/gkgange/geas.git
	# 		cd geas
	# 		make
	# 		cd ..
	# 		curl -L https://bitbucket.org/gkgange/lazycbs/downloads/ECBS_PF.tar.gz > ECBS_PF.tar.gz
	# 		tar -xvzf ECBS_PF.tar.gz
	# 		cd ECBS_PF
	# 		make
	# 		cd ../lazycbs
	# 		make
	# 	SCRIPT
	# end
end