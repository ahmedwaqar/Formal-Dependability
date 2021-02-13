.PHONY: all RBD FT case_studies clean

HOLMAKE = /Users/waqarahmed/HOL/bin/Holmake 
all:    case_studies
	$(HOLMAKE)
RBD:
	cd RBD/ && $(HOLMAKE)

FT:
	cd FT/ && $(HOLMAKE)

case_studies:
	cd case_studies/ && $(HOLMAKE)
clean:
	$(HOLMAKE) cleanAll
	cd RBD/ && $(HOLMAKE) cleanAll && cd ..
	cd FT/ && $(HOLMAKE)cleanAll && cd ..
	cd case_studies/ && $(HOLMAKE) cleanAll && cd ..
