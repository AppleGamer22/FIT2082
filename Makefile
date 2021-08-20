ecbs:
	cd ECBS_PF
	make
geas:
	cd geas
	make
lazycbs:
	cd lazycbs
	make
clean:
	-rm ECBS_PF/libecbs.a
	-rm ECBS_PF/*.o
	-rm geas/libgeas.a
	-rm lazycbs/lazy-cbs