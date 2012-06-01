AC_INIT(marshall,1.0)
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_MACRO_DIR([build-aux])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

AC_PROG_OCAML
if test "$OCAMLBUILD" = "no"; then
  AC_MSG_ERROR([You must install OCaml with ocamlbuild utility])
fi

OCAMLMAJOR=`echo $OCAMLVERSION | cut -d. -f1`
AC_SUBST([OCAMLMAJOR])

OCAMLMINOR=`echo $OCAMLVERSION | cut -d. -f2`
AC_SUBST([OCAMLMINOR])

if test \( "$OCAMLMAJOR" -lt "3" \) -o \( "$OCAMLMAJOR" = "3" -a "$OCAMLMINOR" -lt "12" \) ; then
   AC_MSG_ERROR([Ocaml version 3.12 or higher required])
fi

AC_CHECK_TOOL([OCAMLMENHIR],[menhir],[no])
if test "$OCAMLMENHIR" = "no"; then
    AC_MSG_ERROR([You must install the Ocaml menhir parser generator])
fi

AC_CHECK_TOOLS([WRAPPER],[rlwrap ledit],[no])

AC_SUBST([WRAPPER])

if test "$WRAPPER" = "no"; then
   AC_MSG_WARN([No line-editing wrapper found, we recommend rlwrap or ledit.])
fi

if test "$OCAMLBEST" = "opt"; then
  BUILDBEST=native
else
  BUILDBEST=byte
fi

AC_SUBST([BUILDBEST])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT