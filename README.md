A verified regular expression matching tool in Idris
===================================

A formalized tool for searching using regular expression. This development is based on the article:

[Regular-expression derivatives reexamined](https://www.mpi-sws.org/~turon/re-deriv.pdf)

by Owens et. al.

Usage
-----

    igrep [REGEXP] [FILE_LIST]

where

- REGEXP: Regular expression to be searched.
- FILE_LIST: List of files to be considered for searching.


Syntax of Regular Expressions
------------------------

The syntax of regular expressions is as follows:

    e ::= e + e
       |    e e
       |    e *
       | ( e )
       | c

where c is some character that isn't +, (,) and *.
Note that currently the tool does not support operators like
complement, intersection and the empty set.


Dependencies
-----------

The igrep tool depends on the following Idris libraries:

- [Lightyear](https://github.com/ziman/lightyear), a parser combinator
library for Idris.
- [Effects](https://github.com/idris-lang/Idris-dev/tree/master/libs/effects),
effectful computations in Idris.

Effects library is already shipped within Idris compiler and Lightyear
can be easily installed. Just download the library using the URL above
and execute:

    make clean
    make test
    make install

The development is done using Idris version 0.9.19.
