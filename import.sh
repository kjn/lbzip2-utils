#!/bin/sh
#-
# Copyright (C) 2011, 2012, 2013, 2014 Mikolaj Izdebski
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#

set -e
IFS=' ''	''
'

if ! test -r import.sh; then
  echo import.sh: need to be called from top source directory >&2
  exit 1
fi

import() {
    perl -e'

undef $/;
$_=<>;

s/\(gzip\)/(lbzip2-utils)/g;
s/z\$prog/lbz\$prog/g;
s/\[-\.\]\[zZtga\]\*/[.][tbz2]*/g;
s/\.tgz/.tbz/g;

s/\*\[-\.\]gz\* \| \*\[-\.\]\[zZ\] \| \*\.t\[ga\]z|\*\[-\.\]z \| \*\[-\.\]gz \| \*\.t\[ag\]z/*.bz2 | *.tbz | *.tbz2 | *.tz2/g;

s/gzip -cv9/u=; : | lbzip2 -u &>\/dev\/null && u=u; lbzip2 -c9\$u/g;
s/gzip -cdf?q?/lbzip2 -cdq/g;
s/gzip/lbzip2/g;
s/gunzip/lbunzip2/g;
s/gzexe/lbzexe/g; s/GZEXE/LBZEXE/g;
s/z(cmp|diff|[ef]?grep|force|less|more)/lbz$1/g;
s/Z(cmp|diff|[ef]?grep|force|less|more)/Lbz$1/g;
s/Z(CMP|DIFF|[EF]?GREP|FORCE|LESS|MORE)/LBZ$1/g;
s/, znew\(1\)//g;
s/gz/bz2/g;

s/lbzip2 -lv/head -c4/g;
s/\^defl/BZh[1-9]/g;

s/\n\nReport bugs [^"]*"/"/;

print;

' <$2 >$1
}

import lbzexe.in   gzexe.in
import lbzcmp.in   zcmp.in
import lbzdiff.in  zdiff.in
import lbzgrep.in  zgrep.in
import lbzegrep.in zegrep.in
import lbzfgrep.in zfgrep.in
import lbzforce.in zforce.in
import lbzless.in  zless.in
import lbzmore.in  zmore.in

import lbzexe.1    gzexe.1
import lbzcmp.1    zcmp.1
import lbzdiff.1   zdiff.1
import lbzgrep.1   zgrep.1
import lbzforce.1  zforce.1
import lbzless.1   zless.1
import lbzmore.1   zmore.1

echo .so man1/lbzgrep.1 >lbzegrep.1
echo .so man1/lbzgrep.1 >lbzfgrep.1
