### THIS FILE IS OBSOLETE. READ README.md FOR COMPILATION INSTRUCTIONS.

### CONFIGURATION

# Location of the MPFR library libmpfr.a
MPFRDIR = /usr/lib

# Location of mlgmpidl libraries (such as mpfr.cmx)
MLGMPIDLDIR = /usr/local/lib/ocaml/3.12.0/gmp

# Choose executable names (Linux or Windows)

# Linux (bytecode and native)
EXECUTABLE = marshall_bignum marshall_mpfr dyadic_test
EXECUTABLE_OPT = marshall_bignum.opt marshall_mpfr.opt

# Windows (bytecode and native)
# EXECUTABLE = marshall.exe
# EXECUTABLE_OPT = marshall_opt.exe

#### END OF CONFIGURATION
OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLDEP = ocamldep
OCAMLDOC = ocamldoc
OCAMLWEB = ocamlweb
MENHIR = menhir

# Files which should be included in the documentation
ML_FILES = \
	dyadic.mli \
	dyadic_bignum.ml \
	dyadic_mpfr.ml \
	interval.ml \
	syntax.ml \
	typecheck.ml \
	region.ml \
	environment.ml \
	eval.ml \
	message.ml \
	marshall.ml

# Object files
BYTE_OBJS_SHARED = \
	interval.cmo \
	syntax.cmo \
	message.cmo \
	typecheck.cmo \
	environment.cmo \
	eval.cmo \
	parser.cmo \
	lexer.cmo \
	marshall.cmo

OPT_OBJS_SHARED = $(subst .cmo,.cmx,$(BYTE_OBJS_SHARED))

LIBS = nums.cma
LIBS_OPT = nums.cmxa

LIBS_MPFR = gmp.cma -custom -ccopt "-pthread -L $(MPFRDIR) -L $(MLGMPIDLDIR)" -cclib "-lgmp_caml -lgmp -lmpfr -lbigarray"
LIBS_MPFR_OPT = gmp.cmxa -ccopt "-pthread -L $(MPFRDIR) -L $(MLGMPIDLDIR)" -cclib "-lgmp_caml -lgmp -lmpfr -lbigarray"


OCAMLFLAGS = 
OCAMLOPTFLAGS = 

default: marshall_bignum 

all: marshall_bignum marshall_mpfr marshall_bignum.opt marshall_mpfr.opt marshall.dvi
	echo $(EXECUTABLE_OPT); echo $(EXECUTABLE)
parser.cmo: parser.ml parser.cmi

parser.cmi: parser.mli syntax.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c parser.mli

lexer.cmi: lexer.mli parser.mli message.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c lexer.mli

marshall_bignum: $(BYTE_OBJS_SHARED) dyadic_bignum.cmo marshall_bignum.cmo
	$(OCAMLC) -o $@ $(OCAMLFLAGS) $(LIBS) $+

marshall_bignum.opt: $(OPT_OBJS_SHARED) dyadic_bignum.cmx marshall_bignum.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) $(LIBS_OPT) $+

marshall_mpfr: $(BYTE_OBJS_SHARED) dyadic_mpfr.cmo marshall_mpfr.cmo
	$(OCAMLC) -o $@ $(OCAMLFLAGS) -I $(MLGMPIDLDIR) $(LIBS_MPFR) $+

marshall_mpfr.opt: $(OPT_OBJS_SHARED) dyadic_mpfr.cmx marshall_mpfr.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) -I $(MLGMPIDLDIR) $(LIBS_MPFR_OPT) $+

dyadic_test: dyadic_mpfr.cmo dyadic_bignum.cmo dyadic_test.cmo
	$(OCAMLC) -o $@ $(OCAMLFLAGS) -I $(MLGMPIDLDIR) nums.cma $(LIBS_MPFR) $+

marshall.dvi: $(ML_FILES)
	$(OCAMLWEB) -o marshall.dvi --dvi --short --noweb --header $(ML_FILES)

# Suffixes.
.SUFFIXES: .ml .mli .cmo .cmi .cmx

dyadic_mpfr.cmo: dyadic_mpfr.ml
	$(OCAMLC) $(OCAMLFLAGS) -I $(MLGMPIDLDIR) -c $<

dyadic_test.cmo: dyadic_test.ml
	$(OCAMLC) $(OCAMLFLAGS) -I $(MLGMPIDLDIR) -c $<

dyadic_mpfr.cmx: dyadic_mpfr.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -I $(MLGMPIDLDIR) -c $<

marshall_mpfr.cmo: marshall_mpfr.ml
	$(OCAMLC) $(OCAMLFLAGS) -I $(MLGMPIDLDIR) -c $<

marshall_mpfr.cmx: marshall_mpfr.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -I $(MLGMPIDLDIR) -c $<


%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmi: %.mli $(LIB_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml $(LIB_OPT_OBJS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.ml: %.mll
	$(OCAMLLEX) $<
	$(OCAMLDEP) $(INCLUDES) *.mly *.mll *.mli *.ml > .depend

%.ml %.mli: %.mly
	$(MENHIR) $(OCAMLYFLAGS) $<
	$(OCAMLDEP) $(INCLUDES) *.mly *.mll *.mli *.ml > .depend

# Clean.
clean:
	rm -f $(EXECUTABLE) $(EXECUTABLE_OPT) *.cmi *.cmx *.cmo *.o parser.ml parser.mli lexer.ml lexer.mli

# Depend.
depend:
	$(OCAMLDEP) $(INCLUDES) parser.mly lexer.mll *.mli *.ml > .depend

.PHONY: clean depend

include .depend
