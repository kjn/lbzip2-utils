/*-
  Copyright (C) 2013, 2014 Mikolaj Izdebski

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


/* Knuth–Morris–Pratt algorithm. */
static void
kmp(short d[48][2], const char x[48])
{
  int i, j, c;
  int p[48];

  i = 0;
  j = p[0] = -1;
  while (i < 47) {
    while (j > -1 && x[i] != x[j])
      j = p[j];
    i++, j++;
    p[i] = x[i] == x[j] ? p[j] : j;
  }

  for (i = 0; i < 48; i++)
    for (c = 0; c < 2; c++)
      d[i][c] = (x[i] == c ? i : p[i]) + 1;
}

/* Block magic -- pi in BCD (0x314159265359). */
static const char begin_magic[48] =
  { 0,0,1,1,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,1,1,0,0,1,
    0,0,1,0,0,1,1,0,0,1,0,1,0,0,1,1,0,1,0,1,1,0,0,1 };

/* End of stream magic - sqrt(pi) in BCD (0x177245385090). */
static const char end_magic[48] =
  { 0,0,0,1,0,1,1,1,0,1,1,1,0,0,1,0,0,1,0,0,0,1,0,1,
    0,0,1,1,1,0,0,0,0,1,0,1,0,0,0,0,1,0,0,1,0,0,0,0 };

/* First of three sccepting states of the FSM.  Non-accepting states
   are numbered from 0 to ACCEPT-1.  States ACCEPT through ACCEPT+2 are
   accepting states. */
#define ACCEPT (48*49)

/* DFA transition table. */
static short d[ACCEPT+3][2];

/* Initialize DFA transition table. */
static void
init_dfa(void)
{
  int i, j, c;
  short d1[48][2];

  kmp(d, begin_magic);
  kmp(d1, end_magic);

  for (i = 0; i < 48; i++)
    for (j = 0; j < 48; j++)
      for (c = 0; c < 2; c++)
	d[48+48*i+j][c] = (d[i][c] == 48 ? ACCEPT+1 :
			   d1[j][c] == 48 ? ACCEPT+2 :
			   48+48*d[i][c]+d1[j][c]);

  for (i = 0; i < 48; i++)
    for (c = 0; c < 2; c++)
      if (d[i][c] == 48)
	d[i][c] = ACCEPT;

  for (c = 0; c < 2; c++) {
    d[ACCEPT][c] = d[48][c];
    d[ACCEPT+1][c] = d[48][c];
    d[ACCEPT+2][c] = d[0][c];
  }
}


#if NAME_MAX > 4096
#undef NAME_MAX
#define NAME_MAX 4096
#endif

static const char *pname;
static const char *iname;
static char oname[NAME_MAX];
static int echo;

static FILE *istrm;
static unsigned ibuff;
static unsigned ilive;
static FILE *ostrm;
static uint64_t obuff;
static unsigned olive;

static jmp_buf eof;
static uint32_t crc;

/* Write n (no more than 32) bits to output stream. */
static void
put(int n, uint32_t v)
{
   int i;

   for (i = n-1; i >= 0; i--) {
     obuff = (obuff << 1) | (v >> i);
     if (++olive == 56) {
       if (putc ((uint8_t)(obuff >> 48), ostrm) == EOF) {
	 perror("putc");
	 exit(1);
       }
       olive = 48;
     }
   }
}

/* Read a single bit fron input stream.  On EOF call longjmp(). */
static unsigned
get(void)
{
  int ch;
  unsigned bit;

  if (ilive == 0) {
    if ((ch = getc (istrm)) == EOF) {
      if (ferror(istrm)) {
	perror("getc");
	exit(1);
      }
      longjmp(eof, 1);
    }
    ilive = 8;
    ibuff = ch;
  }
  bit = (ibuff >> --ilive) & 1;
  if (echo)
    put(1, bit);
  return bit;
}

/* Increment a decimal ASCII number stored between p and q. */
static void
increment(char *p, char *q)
{
  int s, c;

  c = 1;
  while (q > p) {
    s = *--q - '0' + c;
    c = 0;
    if (s >= 10)
      s = 0, c = 1;
    *q = s + '0';
  }

  if (c) {
    fprintf(stderr, "%s: too many blocks in the file.\n", pname);
    exit(2);
  }
}

/* Initialize a new block. */
static
void begin(void)
{
  int i;

  increment(oname+3, oname+13);

  ostrm = fopen(oname, "wb");
  if (ostrm == NULL) {
    fprintf(stderr, "%s: unable to open '%s' for writing: %s\n",
	    pname, oname, strerror(errno));
    exit(1);
  }
  fprintf(stderr, "%s: writing reconstructed block to '%s'...\n",
	  pname, oname);

  obuff = 0;
  olive = 0;
  put(32, 0x425A6839UL);
  put(24, 0x314159UL);
  put(24, 0x265359UL);
  echo = 1;

  crc = 0;
  for (i = 0; i < 32; i++)
    crc = (crc << 1) + get();
}

/* Finalize current block. */
static void
end(void)
{
  obuff >>= 48;
  olive -= 48;
  put(24, 0x177245UL);
  put(24, 0x385090UL);
  put(32, crc);
  put(32, 0);
  put(23, 0);

  if (fclose(ostrm) == EOF) {
    perror("fclose");
    exit(1);
  }
  echo = 0;
}


int
main(int argc, char **argv)
{
  int i;
  size_t sz;

  pname = strrchr(argv[0], '/');
  pname = pname ? pname + 1 : argv[0];

  if (argc < 2) {
    fprintf(stderr, "%s: usage: %s file1 [file2 ...]\n", pname, pname);
    exit(1);
  }

  init_dfa();

  for (i = 1; i < argc; i++) {
    iname = argv[i];
    strcpy(oname, "rec0000000000_");
    strncat(oname, iname, NAME_MAX-15);
    sz = strlen(oname);
    if (strcmp(oname+sz-4, ".bz2") != 0) {
      oname[NAME_MAX-19] = '\0';
      strcat(oname, ".bz2");
    }

    if ((istrm = fopen (iname, "rb")) == NULL) {
      fprintf(stderr, "%s: unable to open '%s' for reading: %s\n",
	      pname, iname, strerror(errno));
      exit(1);
    }
    fprintf(stderr, "%s: recovering data from '%s'...\n",
	    pname, iname);

    ibuff = 0;
    ilive = 0;

    if (!setjmp(eof)) {
      unsigned state = 0;

      for (;;) {
	state = d[state][get()];

	if (state >= ACCEPT) {
	  if (state != ACCEPT)
	    end();
	  if (state != ACCEPT+2)
	    begin();
	}
      }
    }

    if (echo)
      end();
    if (fclose(istrm) == EOF) {
      perror("fclose");
      exit(1);
    }
  }

  fprintf(stderr, "%s: done\n", pname);
  return 0;
}
