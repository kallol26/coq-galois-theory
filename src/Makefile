
FILES = ssr nat_lib nati_lib ring
GLOB_FILE = .glob
DOC_DIR = ../doc
WEBSITE_DOC_DIR = ~/save/projects/website/research/projects/galois/doc
SSR_DIR = ../../trunk

V_FILES = $(addsuffix .v,$(FILES))
VO_FILES = $(addsuffix .vo,$(FILES))
HTML_FILES = $(addsuffix .html,$(FILES))

default : $(VO_FILES) $(HTML_FILES)



%.vo : %.v
	ssrcoq -I $(SSR_DIR) -dump-glob $(GLOB_FILE) -compile $*

%.html : %.v
	coqdoc -d $(DOC_DIR) --glob-from $(GLOB_FILE) -l --toc $<
	-cp -Rf $(DOC_DIR)/* $(WEBSITE_DOC_DIR)


clean :
	rm -rf *.vo doc/* $(GLOB_FILE) *~