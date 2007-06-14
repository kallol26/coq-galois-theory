
# where to put documentation
DOC_DIR = ~/save/versioned/website/software/galois/doc

# where the ssreflect library lives
SSR_DIR = ../../../trunk
LIB_DIR = .

#-------------------------------------------------------------------------------
# Do not edit below this line                                                   
#-------------------------------------------------------------------------------

FILES = ssr withzero classical_lib constructive_lib nati lib # withzero # nzring-sig
GLOB_FILE = .glob
V_FILES = $(addsuffix .v,$(FILES))
VO_FILES = $(addsuffix .vo,$(FILES))
HTML_FILES = $(addsuffix .html,$(FILES))

default : $(VO_FILES) 

doc : $(V_FILES)
	coqdoc -d $(DOC_DIR) --glob-from $(GLOB_FILE) -l --toc $(V_FILES)

%.vo : %.v
	ssrcoq -I $(SSR_DIR) -I $(LIB_DIR) -dump-glob $(GLOB_FILE) -compile $*

clean :
	rm -rf *.vo $(DOC_DIR)/* $(GLOB_FILE) *~