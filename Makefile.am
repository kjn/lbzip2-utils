#-
# Copyright (C) 2013 Mikolaj Izdebski
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

EXTRA_DIST = lbzcmp.in lbzdiff.in lbzegrep.in lbzexe.in lbzfgrep.in \
    lbzforce.in lbzgrep.in lbzless.in lbzmore.in \
    lbzcmp.1 lbzdiff.1 lbzegrep.1 lbzexe.1 lbzfgrep.1 \
    lbzforce.1 lbzgrep.1 lbzless.1 lbzmore.1 \
    autogen.sh
#lbzrecover.1

bin_PROGRAMS = lbzrecover
lbzrecover_SOURCES = lbzrecover.c

bin_SCRIPTS = lbzcmp lbzdiff lbzegrep lbzexe lbzfgrep \
    lbzforce lbzgrep lbzless lbzmore
man_MANS = lbzcmp.1 lbzdiff.1 lbzegrep.1 lbzexe.1 lbzfgrep.1 \
    lbzforce.1 lbzgrep.1 lbzless.1 lbzmore.1 #lbzrecover.1
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
