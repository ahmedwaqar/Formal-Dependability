.PHONY: all clean

HOLMAKE = /Users/waqarahmed/HOL/bin/Holmake 
all:
	$(HOLMAKE)

clean:
	$(HOLMAKE) cleanAll
	cd RBD/ && $(HOLMAKE) cleanAll && cd ..
	cd FT/ && $(HOLMAKE)cleanAll && cd ..
	cd case_studies/ && $(HOLMAKE) cleanAll && cd ..
