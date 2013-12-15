#! /bin/bash

grep import */*hs                       \
| grep "Document\.\|Latex\.\|Logic\.\|Theories\.\|UnitB\.\|Utilities\.\|Z3\.[^h]" \
| grep -v -i "test"                     \
| sed "s/[uU]tilities/:0:Utilities/g"   \
| sed "s/Logic/:1:Logic/g"              \
| sed "s/Latex/:1:Latex/g"              \
| sed "s/ Z3/ :2:Z3/g"                  \
| sed "s/^Z3/:2:Z3/g"                   \
| sed "s/Theories/:2:Theories/g"        \
| sed "s/UnitB/:3:UnitB/g"              \
| sed "s/Document/:4:Document/g"        \
| sort                                  \
