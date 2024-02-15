
# Open dumped waveform with GTKWave
.PHONY: waves-mattia
waves-mattia: 
	$(shell scp ./build/sim-common/waves.fst sca.user@pc-lse-1861.polito.it:/home/sca.user/Desktop/Len5)
	$(shell ssh sca.user@pc-lse-1861.polito.it "cd /home/sca.user/Desktop/Len5 && make")
	