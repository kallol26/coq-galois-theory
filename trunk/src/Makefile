
FILES = galois
GLOB_FILE = .glob
DOC_DIR = ../doc
SSR_DIR = ../../trunk

V_FILES = $(addsuffix .v,$(FILES))
VO_FILES = $(addsuffix .vo,$(FILES))
HTML_FILES = $(addsuffix .html,$(FILES))

default : $(VO_FILES) $(HTML_FILES)



%.vo : %.v
	ssrcoq -I $(SSR_DIR) -dump-glob $(GLOB_FILE) -compile $*

%.html : %.v
	coqdoc -d $(DOC_DIR) --glob-from $(GLOB_FILE) $<


clean :
	rm -rf *.vo doc/* $(GLOB_FILE) *~