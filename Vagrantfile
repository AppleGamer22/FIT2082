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
end