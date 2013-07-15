/*-
  lbzmerge, version 2
  7 November 2011

  Copyright (C) 2011 Mikolaj Izdebski <zurgunt@gmail.com>
                                                                          
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

/* `lbzmerge' reads compressed data in bzip2 format, merges any streams found
   and writes the result to stdout. Any command-line options are ignored.

   Older versions of lbzip2 (pre 2.0) used to create multiple streams per file,
   which could cause some problems. This program allows you to work around
   this incompatibility. It also can be used to trim any trailing garbage.

   This program is written for readability, not performance -- simpler but
   slower algorithms were chosen deliberately.

   This code targets ANSI C systems, but it was tested only very roughly.
*/

#ifdef HAVE_CONFIG_H
# include <config.h>
#endif

#include <stdio.h>   /* getchar() */
#include <stdlib.h>  /* exit() */

static void err(const char *msg) {
  fprintf(stderr, "lbzmerge: ");
  if (msg) perror(msg);
  exit(EXIT_FAILURE);
}

/* Read a single byte from stdin. */
static int read(void) {
  int c;
  if ((c = getchar()) != EOF) return c;
  if (!feof(stdin)) err("getchar()");
  return -1;
}

/* Write a single byte to stdout. */
static void write(int c) {
  if (putchar(c) == EOF)
    err("putchar()");
}

/* Print an error message and terminate. */
static void bad(void) {
  fprintf(stderr, "minbzcat: data error in bz2 file\n");
  exit(EXIT_FAILURE);
}


static int bb;      /* input bit-buffer (static, right-aligned) */
static int bk;      /* number of bits remaining in the `bb' bit-buffer */
static int wb = 1;  /* output bit-buffer (dynamic, right-aligned) */

static unsigned long mbs;  /* maximal block size (100k-900k in 100k steps) */
static unsigned short as;  /* alphabet size (number of distinct prefix codes,
                              3-258) */
static unsigned short nt;  /* number of prefix trees used for current block
                              (2-6) */
static unsigned short ns;  /* number of selectors (1-32767) */
static unsigned long nm;   /* number of MTF values */

static unsigned char len[6][259];   /* code lengths for different trees
                                       (element 258 is a sentinel) */
static unsigned char sel[32767];    /* selector MTF values */
static unsigned char mtf[256];      /* IMTF register */
static unsigned short count[21];    /* number of codes of given length
                                       (element 0 is a sentinel) */
static unsigned short sorted[258];  /* symbols sorted by ascend. code length */


/* Write `n' lowest bits of `x' to stdout. */
static void put(int n, unsigned long x) {
  while (n--) {
    wb = 2*wb + ((x >> n) & 1);
    if (wb >= 256) { write(wb & 0xff); wb = 1; }
  }
}

/* Read and return `n' bits from the input stream. `n' must be <= 32. */
static unsigned long getn(int n) {
  unsigned long x = 0;
  while (n--) {
    if (!bk-- && (bb = read()) < 0) bad();
    x = 2*x + ((bb >> (bk &= 7)) & 1);
  }
  return x;
}

/* Same as getn(), but also echo to stdout bits read. */
static unsigned long get(int n) {
  unsigned long x = getn(n);
  put(n,x);
  return x;
}

/* Create decode tables using code lengths from `lens[t]'.
   `t' is the tree selector, must be in range [0,nt). */
static void make_tree(int t) {
  unsigned short u[21], i, s, a;
  for (i = 0; i <= 20; i++)
    count[i] = 0;
  for (i = 0; i < as; i++)
    count[len[t][i]]++;
  for (a = 1, s = 0, i = 0; i <= 20; i++) {
    u[i] = s;
    a *= 2;
    if (count[i] > a) bad();
    a -= count[i];
    s += count[i];
  }
  for (i = 0; i < as; i++)
    sorted[u[len[t][i]]++] = i;
}

/* Decode a single prefix code. The algorithm used is naive and slow. */
static unsigned get_sym(void) {
  int s = 0, x = 0, k = 0;
  do {
    if (k == 20) bad();
    x = 2*x + get(1);
    s += count[++k];
  } while ((x -= count[k]) >= 0);
  return sorted[s + x];
}

/* Retrieve bitmap. */
static void bmp(void) {
  unsigned i, j;
  unsigned short b = get(16);
  as = 0;
  for (i = 0; i < 16; i++) {
    if (b & 0x8000) {
      unsigned short s = get(16);
      for (j = 0; j < 16; j++) {
        if (s & 0x8000)
          mtf[as++] = 16*i + j;
        s *= 2;
      }
    }
    b *= 2;
  }
  as += 2;
}

/* Retrieve selector MTF values. */
static void smtf(void) {
  unsigned g;
  for (g = 0; g < ns; g++) {
    sel[g] = 0;
    while (sel[g] < nt && get(1))
      sel[g]++;
    if (sel[g] == nt) bad();
  }
  if (ns > 18001)
    ns = 18001;
}

/* Retrieve code lengths. */
static void trees(void) {
  unsigned t,s;
  for (t = 0; t < nt; t++) {
    len[t][0] = get(5);
    for (s = 0; s < as; s++) {
      goto in;
      do {
        len[t][s] += 1 - 2*get(1);
      in:
        if (len[t][s] < 1 || len[t][s] > 20) bad();
      } while (get(1));
      len[t][s+1] = len[t][s];
    }
  }
}

/* Retrieve block MTF values. */
static void data(void) {
  unsigned g,i,t;
  unsigned m[6];
  for (i = 0; i < 6; i++)
    m[i] = i;
  nm = 0;
  for (g = 0; g < ns; g++) {
    i = sel[g];
    t = m[i];
    while (i-- > 0)
      m[i+1] = m[i];
    m[0] = t;
    make_tree(t);
    for (i = 0; i < 50; i++)
      if (get_sym() == as-1u)
        return;
  }
  bad();
}

/* Retrieve block. */
static void retr(void) {
  get(1+24); /* rnd+idx */
  bmp();
  nt = get(3);
  if (nt < 2 || nt > 6) bad();
  ns = get(15);
  smtf();
  trees();
  data();
}

/* Parse stream and bock headers, merge any streams found. */
int main(void) {
  unsigned long t = 0, c, cc = 0;
  put(32,0x425A6839);
  if (getn(24) != 0x425A68) bad();
  do {
    c = 0;
    t = getn(8) - 0x31;
    if (t >= 9) bad();
    mbs = 100000 * (t+1);
    while ((t = getn(16)) == 0x3141) {
      if (getn(32) != 0x59265359) bad();
      put(16,0x3141);
      put(32,0x59265359);
      t = get(32);
      c = ((c << 1) & 0xFFFFFFFF) ^ (c >> 31) ^ t;
      cc = ((cc << 1) & 0xFFFFFFFF) ^ (cc >> 31) ^ t;
      retr();
    }
    if (t != 0x1772) bad();
    if (getn(32) != 0x45385090) bad();
    if (getn(32) != c) bad();
    bk = 0;
  } while (read() == 0x42 && read() == 0x5A && read() == 0x68);
  put(16,0x1772);
  put(32,0x45385090);
  put(32,cc);
  put(7,0);
  if (fclose(stdin) == EOF) err("fclose(stdin)");
  if (fclose(stdout) == EOF) err("fclose(stdout)");
  return EXIT_SUCCESS;
}
