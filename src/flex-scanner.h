/* Common parts between scan-code.l and scan-gram.l.

   Copyright (C) 2006 Free Software Foundation, Inc.

   This file is part of Bison, the GNU Compiler Compiler.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301  USA
*/

#ifndef FLEX_PREFIX
# error "FLEX_PREFIX not defined"
#endif

#include "system.h"

/* Pacify "gcc -Wmissing-prototypes" when flex 2.5.31 is used.  */
int   FLEX_PREFIX (get_lineno) (void);
FILE *FLEX_PREFIX (get_in) (void);
FILE *FLEX_PREFIX (get_out) (void);
int   FLEX_PREFIX (get_leng) (void);
char *FLEX_PREFIX (get_text) (void);
void  FLEX_PREFIX (set_lineno) (int);
void  FLEX_PREFIX (set_in) (FILE *);
void  FLEX_PREFIX (set_out) (FILE *);
int   FLEX_PREFIX (get_debug) (void);
void  FLEX_PREFIX (set_debug) (int);
int   FLEX_PREFIX (lex_destroy) (void);

#define last_string    FLEX_PREFIX (last_string)

/* It seems to be a nice "feature" of Flex that one cannot use yytext,
   yyleng etc. when a prefix is given, since there is no longer a
   #define, but rather the token is actually changed in the output.
   */
#define yyleng  FLEX_PREFIX (leng)
#define yytext  FLEX_PREFIX (text)

/* OBSTACK_FOR_STRING -- Used to store all the characters that we need to
   keep (to construct ID, STRINGS etc.).  Use the following macros to
   use it.

   Use STRING_GROW to append what has just been matched, and
   STRING_FINISH to end the string (it puts the ending 0).
   STRING_FINISH also stores this string in LAST_STRING, which can be
   used, and which is used by STRING_FREE to free the last string.  */

static struct obstack obstack_for_string;

#define STRING_GROW   \
  obstack_grow (&obstack_for_string, yytext, yyleng)

#define STRING_FINISH					\
  do {							\
    obstack_1grow (&obstack_for_string, '\0');		\
    last_string = obstack_finish (&obstack_for_string);	\
  } while (0)

#define STRING_FREE \
  obstack_free (&obstack_for_string, FLEX_PREFIX (last_string))