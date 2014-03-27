#-
# Copyright (C) 2013, 2014 Mikolaj Izdebski
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

EXTRA_DIST = \
    lbzexe.in   gzexe.in   lbzexe.1    gzexe.1   \
    lbzcmp.in   zcmp.in    lbzcmp.1    zcmp.1    \
    lbzdiff.in  zdiff.in   lbzdiff.1   zdiff.1   \
    lbzgrep.in  zgrep.in   lbzgrep.1   zgrep.1   \
    lbzegrep.in zegrep.in  lbzegrep.1            \
    lbzfgrep.in zfgrep.in  lbzfgrep.1            \
    lbzforce.in zforce.in  lbzforce.1  zforce.1  \
    lbzless.in  zless.in   lbzless.1   zless.1   \
    lbzmore.in  zmore.in   lbzmore.1   zmore.1   \
    \
    lbzrecover.1 \
    import.sh autogen.sh

bin_PROGRAMS = lbzmerge lbzrecover
lbzmerge_SOURCES = lbzmerge.c
lbzrecover_SOURCES = lbzrecover.c

bin_SCRIPTS = lbzcmp lbzdiff lbzegrep lbzexe lbzfgrep \
    lbzforce lbzgrep lbzless lbzmore
man_MANS = lbzcmp.1 lbzdiff.1 lbzegrep.1 lbzexe.1 lbzfgrep.1 \
    lbzforce.1 lbzgrep.1 lbzless.1 lbzmore.1 lbzrecover.1
MOSTLYCLEANFILES = lbzcmp lbzdiff lbzegrep lbzexe lbzfgrep \
    lbzforce lbzgrep lbzless lbzmore

SUFFIXES = .in
.in:
	$(AM_V_GEN)sed \
    -e 's|/bin/sh|$(SHELL)|g' \
    -e 's|[@]bindir@|'\''$(bindir)'\''|g' \
    -e 's|[@]GREP@|$(GREP)|g' \
    -e 's|[@]VERSION@|$(VERSION)|g' \
    $(srcdir)/$@.in >$@-t \
    && chmod a+x $@-t \
    && mv $@-t $@
