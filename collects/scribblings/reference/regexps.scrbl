#lang scribble/doc
@(require scribble/bnf "mz.rkt" "rx.rkt")

@title[#:tag "regexp"]{Regular Expressions}

@section-index{regexps}
@section-index{pattern matching}
@section-index["strings" "pattern matching"]
@section-index["input ports" "pattern matching"]

@guideintro["regexp"]{regular expressions}

@deftech{Regular expressions} are specified as strings or byte
strings, using the same pattern language as the Unix utility
@exec{egrep} or Perl. A string-specified pattern produces a character
regexp matcher, and a byte-string pattern produces a byte regexp
matcher. If a character regexp is used with a byte string or input
port, it matches UTF-8 encodings (see @secref["encodings"]) of
matching character streams; if a byte regexp is used with a character
string, it matches bytes in the UTF-8 encoding of the string.

Regular expressions can be compiled into a @deftech{regexp value} for
repeated matches. The @racket[regexp] and @racket[byte-regexp]
procedures convert a string or byte string (respectively) into a
regexp value using one syntax of regular expressions that is most
compatible to @exec{egrep}. The @racket[pregexp] and
@racket[byte-pregexp] procedures produce a regexp value using a
slightly different syntax of regular expressions that is more
compatible with Perl.  In addition, Racket constants written with
@litchar{#rx} or @litchar{#px} (see @secref["reader"]) produce
compiled regexp values.

The internal size of a regexp value is limited to 32 kilobytes; this
limit roughly corresponds to a source string with 32,000 literal
characters or 5,000 operators.

@;------------------------------------------------------------------------
@section[#:tag "regexp-syntax"]{Regexp Syntax}

The following syntax specifications describe the content of a string
that represents a regular expression. The syntax of the corresponding
string may involve extra escape characters. For example, the regular
expression @litchar{(.*)\1} can be represented with the string
@racket["(.*)\\1"] or the regexp constant @racket[#rx"(.*)\\1"]; the
@litchar{\} in the regular expression must be escaped to include it
in a string or regexp constant.

The @racket[regexp] and @racket[pregexp] syntaxes share a common core:

@common-table

The following completes the grammar for @racket[regexp], which treats
@litchar["{"] and @litchar["}"] as literals, @litchar{\} as a
literal within ranges, and @litchar{\} as a literal producer
outside of ranges.

@rx-table

The following completes the grammar for @racket[pregexp], which uses
@litchar["{"] and @litchar["}"] bounded repetition and uses
@litchar{\} for meta-characters both inside and outside of ranges.

@px-table

The Unicode categories follow.

@category-table

@;------------------------------------------------------------------------
@section{Additional Syntactic Constraints}

In addition to matching a grammar, regular expressions must meet two
syntactic restrictions:

@itemize[

 @item{In a @nonterm{repeat} other than @nonterm{atom}@litchar{?},
       the @nonterm{atom} must not match an empty sequence.}

 @item{In a @litchar{(?<=}@nonterm{regexp}@litchar{)} or
       @litchar{(?<!}@nonterm{regexp}@litchar{)},
       the @nonterm{regexp} must match a bounded sequence only.}

]

These contraints are checked syntactically by the following type
system. A type [@math{n}, @math{m}] corresponds to an expression that
matches between @math{n} and @math{m} characters. In the rule for
@litchar{(}@nonterm{Regexp}@litchar{)}, @math{N} means the number such
that the opening parenthesis is the @math{N}th opening parenthesis for
collecting match reports.  Non-emptiness is inferred for a
backreference pattern, @litchar{\}@nonterm{N}, so that a
backreference can be used for repetition patterns; in the case of
mutual dependencies among backreferences, the inference chooses the
fixpoint that maximizes non-emptiness.  Finiteness is not inferred for
backreferences (i.e., a backreference is assumed to match an
arbitrarily large sequence).

@type-table

@;------------------------------------------------------------------------
@section{Regexp Constructors}

@defproc[(regexp? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{regexp value} created by
@racket[regexp] or @racket[pregexp], @racket[#f] otherwise.}


@defproc[(pregexp? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{regexp value} created by
@racket[pregexp] (not @racket[regexp]), @racket[#f] otherwise.}


@defproc[(byte-regexp? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{regexp value} created by
@racket[byte-regexp] or @racket[byte-pregexp], @racket[#f] otherwise.}


@defproc[(byte-pregexp? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{regexp value} created by
@racket[byte-pregexp] (not @racket[byte-regexp]), @racket[#f]
otherwise.}


@defproc[(regexp [str string?]) regexp?]{

Takes a string representation of a regular expression (using the
syntax in @secref["regexp-syntax"]) and compiles it into a @tech{regexp
value}. Other regular expression procedures accept either a string or a
@tech{regexp value} as the matching pattern. If a regular expression string
is used multiple times, it is faster to compile the string once to a
@tech{regexp value} and use it for repeated matches instead of using the
string each time.

The @racket[object-name] procedure returns
the source string for a @tech{regexp value}.

@examples[
(regexp "ap*le")
(object-name #rx"ap*le")
]}

@defproc[(pregexp [string string?]) pregexp?]{

Like @racket[regexp], except that it uses a slightly different syntax
(see @secref["regexp-syntax"]). The result can be used with
@racket[regexp-match], etc., just like the result from
@racket[regexp].

@examples[
(pregexp "ap*le")
(regexp? #px"ap*le")
]}

@defproc[(byte-regexp [bstr bytes?]) byte-regexp?]{

Takes a byte-string representation of a regular expression (using the
syntax in @secref["regexp-syntax"]) and compiles it into a
byte-@tech{regexp value}.

The @racket[object-name] procedure
returns the source byte string for a @tech{regexp value}.

@examples[
(byte-regexp #"ap*le")
(object-name #rx#"ap*le")
(byte-regexp "ap*le")
]}

@defproc[(byte-pregexp [bstr bytes?]) byte-pregexp?]{

Like @racket[byte-regexp], except that it uses a slightly different
syntax (see @secref["regexp-syntax"]). The result can be used with
@racket[regexp-match], etc., just like the result from
@racket[byte-regexp].

@examples[
(byte-pregexp #"ap*le")
]}

@defproc*[([(regexp-quote [str string?] [case-sensitive? any/c #t]) string?]
           [(regexp-quote [bstr bytes?] [case-sensitive? any/c #t]) bytes?])]{

Produces a string or byte string suitable for use with @racket[regexp]
to match the literal sequence of characters in @racket[str] or
sequence of bytes in @racket[bstr]. If @racket[case-sensitive?] is
true (the default), the resulting regexp matches letters in
@racket[str] or @racket[bytes] case-sensitively, otherwise it matches
case-insensitively.

@examples[
(regexp-match "." "apple.scm")
(regexp-match (regexp-quote ".") "apple.scm")
]}

@defproc[(regexp-max-lookbehind [pattern (or/c regexp? byte-regexp?)])
         exact-nonnegative-integer?]{

Returns the maximum number of bytes that @racket[pattern] may consult
before the starting position of a match to determine the match. For
example, the pattern @litchar{(?<=abc)d} consults three bytes
preceding a matching @litchar{d}, while @litchar{e(?<=a..)d} consults
two bytes before a matching @litchar{ed}. A @litchar{^} pattern may
consult a preceding byte to determine whether the current position is
the start of the input or of a line.}

@;------------------------------------------------------------------------
@section{Regexp Matching}

@defproc[(regexp-match [pattern (or/c string? bytes? regexp? byte-regexp?)]
                       [input (or/c string? bytes? path? input-port?)]
                       [start-pos exact-nonnegative-integer? 0]
                       [end-pos (or/c exact-nonnegative-integer? #f) #f]
                       [output-port (or/c output-port? #f) #f]
                       [input-prefix bytes? #""])
         (if (and (or (string? pattern) (regexp? pattern))
                  (or (string? input) (path? input)))
             (or/c #f (cons/c string? (listof (or/c string? #f))))
             (or/c #f (cons/c bytes?  (listof (or/c bytes?  #f)))))]{

Attempts to match @racket[pattern] (a string, byte string,
@tech{regexp value}, or byte-@tech{regexp value}) once to a portion of
@racket[input].  The matcher finds a portion of @racket[input] that
matches and is closest to the start of the input (after
@racket[start-pos]).

If @racket[input] is a path, it is converted to a byte string with
@racket[path->bytes] if @racket[pattern] is a byte string or a
byte-based regexp. Otherwise, @racket[input] is converted to a string
with @racket[path->string].

The optional @racket[start-pos] and @racket[end-pos] arguments select
a portion of @racket[input] for matching; the default is the entire
string or the stream up to an end-of-file. When @racket[input] is a
string, @racket[start-pos] is a character position; when
@racket[input] is a byte string, then @racket[start-pos] is a byte
position; and when @racket[input] is an input port, @racket[start-pos]
is the number of bytes to skip before starting to match. The
@racket[end-pos] argument can be @racket[#f], which corresponds to the
end of the string or an end-of-file in the stream; otherwise, it is a
character or byte position, like @racket[start-pos]. If @racket[input]
is an input port, and if an end-of-file is reached before
@racket[start-pos] bytes are skipped, then the match fails.

In @racket[pattern], a start-of-string @litchar{^} refers to the first
position of @racket[input] after @racket[start-pos], assuming that
@racket[input-prefix] is @racket[#""].  The end-of-input @litchar{$}
refers to the @racket[end-pos]th position or (in the case of an input
port) an end-of-file, whichever comes first.

The @racket[input-prefix] specifies bytes that effectively precede
@racket[input] for the purposes of @litchar{^} and other look-behind
matching. For example, a @racket[#""] prefix means that @litchar{^}
matches at the beginning of the stream, while a @racket[#"\n"]
@racket[input-prefix] means that a start-of-line @litchar{^} can match
the beginning of the input, while a start-of-file @litchar{^} cannot.

If the match fails, @racket[#f] is returned. If the match succeeds, a
list containing strings or byte string, and possibly @racket[#f], is
returned. The list contains strings only if @racket[input] is a string
and @racket[pattern] is not a byte regexp. Otherwise, the list
contains byte strings (substrings of the UTF-8 encoding of
@racket[input], if @racket[input] is a string).

The first [byte] string in a result list is the portion of
@racket[input] that matched @racket[pattern]. If two portions of
@racket[input] can match @racket[pattern], then the match that starts
earliest is found.

Additional [byte] strings are returned in the list if @racket[pattern]
contains parenthesized sub-expressions (but not when the opening
parenthesis is followed by @litchar{?}). Matches for the
sub-expressions are provided in the order of the opening parentheses
in @racket[pattern]. When sub-expressions occur in branches of an
@litchar{|} ``or'' pattern, in a @litchar{*} ``zero or more''
pattern, or other places where the overall pattern can succeed without
a match for the sub-expression, then a @racket[#f] is returned for the
sub-expression if it did not contribute to the final match. When a
single sub-expression occurs within a @litchar{*} ``zero or more''
pattern or other multiple-match positions, then the rightmost match
associated with the sub-expression is returned in the list.

If the optional @racket[output-port] is provided as an output port,
the part of @racket[input] from its beginning (not @racket[start-pos])
that precedes the match is written to the port. All of @racket[input]
up to @racket[end-pos] is written to the port if no match is
found. This functionality is most useful when @racket[input] is an
input port.

When matching an input port, a match failure reads up to
@racket[end-pos] bytes (or end-of-file), even if @racket[pattern]
begins with a start-of-string @litchar{^}; see also
@racket[regexp-try-match]. On success, all bytes up to and including
the match are eventually read from the port, but matching proceeds by
first peeking bytes from the port (using @racket[peek-bytes-avail!]),
and then (re@-~-)reading matching bytes to discard them after the match
result is determined. Non-matching bytes may be read and discarded
before the match is determined. The matcher peeks in blocking mode
only as far as necessary to determine a match, but it may peek extra
bytes to fill an internal buffer if immediately available (i.e.,
without blocking). Greedy repeat operators in @racket[pattern], such
as @litchar{*} or @litchar{+}, tend to force reading the entire
content of the port (up to @racket[end-pos]) to determine a match.

If the input port is read simultaneously by another thread, or if the
port is a custom port with inconsistent reading and peeking procedures
(see @secref["customport"]), then the bytes that are peeked and
used for matching may be different than the bytes read and discarded
after the match completes; the matcher inspects only the peeked
bytes. To avoid such interleaving, use @racket[regexp-match-peek]
(with a @racket[progress-evt] argument) followed by
@racket[port-commit-peeked].

@examples[
(regexp-match #rx"x." "12x4x6")
(regexp-match #rx"y." "12x4x6")
(regexp-match #rx"x." "12x4x6" 3)
(regexp-match #rx"x." "12x4x6" 3 4)
(regexp-match #rx#"x." "12x4x6")
(regexp-match #rx"x." "12x4x6" 0 #f (current-output-port))
(regexp-match #rx"(-[0-9]*)+" "a-12--345b")
]}


@defproc[(regexp-match* [pattern (or/c string? bytes? regexp? byte-regexp?)]
                        [input (or/c string? bytes? path? input-port?)]
                        [start-pos exact-nonnegative-integer? 0]
                        [end-pos (or/c exact-nonnegative-integer? #f) #f]
                        [input-prefix bytes? #""])
         (if (and (or (string? pattern) (regexp? pattern))
                  (or (string? input) (path? input)))
             (listof string?)
             (listof bytes?))]{

Like @racket[regexp-match], but the result is a list of strings or
byte strings corresponding to a sequence of matches of
@racket[pattern] in @racket[input]. (Unlike @racket[regexp-match],
results for parenthesized sub-patterns in @racket[pattern] are not
returned.)

The @racket[pattern] is used in order to find matches, where each
match attempt starts at the end of the last match, and @litchar{^} is
allowed to match the beginning of the input (if @racket[input-prefix]
is @racket[#""]) only for the first match.  Empty matches are handled
like other matches, returning a zero-length string or byte sequence
(they are more useful in the complementing @racket[regexp-split]
function), but @racket[pattern] is restricted from matching an empty
sequence immediately after an empty match.

If @racket[input] contains no matches (in the range @racket[start-pos]
to @racket[end-pos]), @racket[null] is returned. Otherwise, each item
in the resulting list is a distinct substring or byte sequence from
@racket[input] that matches @racket[pattern]. The @racket[end-pos]
argument can be @racket[#f] to match to the end of @racket[input]
(which corresponds to an end-of-file if @racket[input] is an input
port).

@examples[
(regexp-match* #rx"x." "12x4x6")
(regexp-match* #rx"x*" "12x4x6")
]}


@defproc[(regexp-try-match [pattern (or/c string? bytes? regexp? byte-regexp?)]
                           [input input-port?]
                           [start-pos exact-nonnegative-integer? 0]
                           [end-pos (or/c exact-nonnegative-integer? #f) #f]
                           [output-port (or/c output-port? #f) #f]
                           [input-prefix bytes? #""])
         (if (and (or (string? pattern) (regexp? pattern))
                  (string? input))
             (or/c #f (cons/c string? (listof (or/c string? #f))))
             (or/c #f (cons/c bytes?  (listof (or/c bytes?  #f)))))]{

Like @racket[regexp-match] on input ports, except that if the match
fails, no characters are read and discarded from @racket[in].

This procedure is especially useful with a @racket[pattern] that
begins with a start-of-string @litchar{^} or with a non-@racket[#f]
@racket[end-pos], since each limits the amount of peeking into the
port. Otherwise, beware that a large portion of the stream may be
peeked (and therefore pulled into memory) before the match succeeds or
fails.}


@defproc[(regexp-match-positions [pattern (or/c string? bytes? regexp? byte-regexp?)]
                                 [input (or/c string? bytes? path? input-port?)]
                                 [start-pos exact-nonnegative-integer? 0]
                                 [end-pos (or/c exact-nonnegative-integer? #f) #f]
                                 [output-port (or/c output-port? #f) #f]
                                 [input-prefix bytes? #""])
          (or/c (cons/c (cons/c exact-nonnegative-integer?
                                exact-nonnegative-integer?)
                        (listof (or/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      #f)))
                #f)]{

Like @racket[regexp-match], but returns a list of number pairs (and
@racket[#f]) instead of a list of strings. Each pair of numbers refers
to a range of characters or bytes in @racket[input]. If the result for
the same arguments with @racket[regexp-match] would be a list of byte
strings, the resulting ranges correspond to byte ranges; in that case,
if @racket[input] is a character string, the byte ranges correspond to
bytes in the UTF-8 encoding of the string.

Range results are returned in a @racket[substring]- and
@racket[subbytes]-compatible manner, independent of
@racket[start-pos]. In the case of an input port, the returned
positions indicate the number of bytes that were read, including
@racket[start-pos], before the first matching byte.

@examples[
(regexp-match-positions #rx"x." "12x4x6")
(regexp-match-positions #rx"x." "12x4x6" 3)
(regexp-match-positions #rx"(-[0-9]*)+" "a-12--345b")
]}

@defproc[(regexp-match-positions* [pattern (or/c string? bytes? regexp? byte-regexp?)]
                                  [input (or/c string? bytes? path? input-port?)]
                                  [start-pos exact-nonnegative-integer? 0]
                                  [end-pos (or/c exact-nonnegative-integer? #f) #f]
                                  [input-prefix bytes? #""])
         (listof (cons/c exact-nonnegative-integer?
                         exact-nonnegative-integer?))]{

Like @racket[regexp-match-positions], but returns multiple matches
like @racket[regexp-match*].

@examples[
(regexp-match-positions* #rx"x." "12x4x6")
]}


@defproc[(regexp-match? [pattern (or/c string? bytes? regexp? byte-regexp?)]
                        [input (or/c string? bytes? path? input-port?)]
                        [start-pos exact-nonnegative-integer? 0]
                        [end-pos (or/c exact-nonnegative-integer? #f) #f]
                        [output-port (or/c output-port? #f) #f]
                        [input-prefix bytes? #""])
           boolean?]{

Like @racket[regexp-match], but returns merely @racket[#t] when the
match succeeds, @racket[#f] otherwise.

@examples[
(regexp-match? #rx"x." "12x4x6")
(regexp-match? #rx"y." "12x4x6")
]}


@defproc[(regexp-match-exact? [pattern (or/c string? bytes? regexp? byte-regexp?)]
                              [input (or/c string? bytes? path?)])
          boolean?]{

Like @racket[regexp-match?], but @racket[#t] is only returned when the
entire content of @racket[input] matches @racket[pattern].

@examples[
(regexp-match-exact? #rx"x." "12x4x6")
(regexp-match-exact? #rx"1.*x." "12x4x6")
]}


@defproc[(regexp-match-peek [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""])
          (or/c (cons/c bytes? (listof (or/c bytes? #f)))
                #f)]{

Like @racket[regexp-match] on input ports, but only peeks bytes from
@racket[input] instead of reading them. Furthermore, instead of
an output port, the last optional argument is a progress event for
@racket[input] (see @racket[port-progress-evt]). If @racket[progress]
becomes ready, then the match stops peeking from @racket[input]
and returns @racket[#f]. The @racket[progress] argument can be
@racket[#f], in which case the peek may continue with inconsistent
information if another process meanwhile reads from
@racket[input].

@examples[
(define p (open-input-string "a abcd"))
(regexp-match-peek ".*bc" p)
(regexp-match-peek ".*bc" p 2)
(regexp-match ".*bc" p 2)
(peek-char p)
(regexp-match ".*bc" p)
(peek-char p)
]}


@defproc[(regexp-match-peek-positions [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""])
          (or/c (cons/c (cons/c exact-nonnegative-integer?
                                exact-nonnegative-integer?)
                        (listof (or/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      #f)))
                #f)]{

Like @racket[regexp-match-positions] on input ports, but only peeks
bytes from @racket[input] instead of reading them, and with a
@racket[progress] argument like @racket[regexp-match-peek].}


@defproc[(regexp-match-peek-immediate [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""])
          (or/c (cons/c bytes? (listof (or/c bytes? #f)))
                #f)]{

Like @racket[regexp-match-peek], but it attempts to match only bytes
that are available from @racket[input] without blocking.  The
match fails if not-yet-available characters might be used to match
@racket[pattern].}


@defproc[(regexp-match-peek-positions-immediate [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""])
          (or/c (cons/c (cons/c exact-nonnegative-integer?
                                exact-nonnegative-integer?)
                        (listof (or/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      #f)))
                #f)]{

Like @racket[regexp-match-peek-positions], but it attempts to match
only bytes that are available from @racket[input] without
blocking. The match fails if not-yet-available characters might be
used to match @racket[pattern].}


@defproc[(regexp-match-peek-positions* [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [input-prefix bytes? #""])
         (listof (cons/c exact-nonnegative-integer?
                         exact-nonnegative-integer?))]{

Like @racket[regexp-match-peek-positions], but returns multiple matches like
@racket[regexp-match*].}

@defproc[(regexp-match/end [pattern (or/c string? bytes? regexp? byte-regexp?)]
                       [input (or/c string? bytes? path? input-port?)]
                       [start-pos exact-nonnegative-integer? 0]
                       [end-pos (or/c exact-nonnegative-integer? #f) #f]
                       [output-port (or/c output-port? #f) #f]
                       [input-prefix bytes? #""]
                       [count nonnegative-exact-integer? 1])
         (values
          (if (and (or (string? pattern) (regexp? pattern))
                   (or/c (string? input) (path? input)))
              (or/c #f (cons/c string? (listof (or/c string? #f))))
              (or/c #f (cons/c bytes?  (listof (or/c bytes?  #f)))))
          (or/c #f bytes?))]{

Like @racket[regexp-match], but with a second result: a byte
string of up to @racket[count] bytes that correspond to the input
(possibly including the @racket[input-prefix]) leading to the end of
the match; the second result is @racket[#f] if no match is found.

The second result can be useful as an @racket[input-prefix] for
attempting a second match on @racket[input] starting from the end of
the first match. In that case, use @racket[regexp-max-lookbehind]
to determine an appropriate value for @racket[count].}

@deftogether[(
@defproc[(regexp-match-positions/end [pattern (or/c string? bytes? regexp? byte-regexp?)]
                                  [input (or/c string? bytes? path? input-port?)]
                                  [start-pos exact-nonnegative-integer? 0]
                                  [end-pos (or/c exact-nonnegative-integer? #f) #f]
                                  [input-prefix bytes? #""]
                                  [count exact-nonnegative-integer? 1])
         (values (listof (cons/c exact-nonnegative-integer?
                                 exact-nonnegative-integer?))
                 (or/c #f bytes?))]
@defproc[(regexp-match-peek-positions/end [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""]
                            [count exact-nonnegative-integer? 1])
         (values
          (or/c (cons/c (cons/c exact-nonnegative-integer?
                                exact-nonnegative-integer?)
                        (listof (or/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      #f)))
                #f)
          (or/c #f bytes?))]
@defproc[(regexp-match-peek-positions-immediate/end [pattern (or/c string? bytes? regexp? byte-regexp?)]
                            [input input-port?]
                            [start-pos exact-nonnegative-integer? 0]
                            [end-pos (or/c exact-nonnegative-integer? #f) #f]
                            [progress (or/c evt #f) #f]
                            [input-prefix bytes? #""]
                            [count exact-nonnegative-integer? 1])
         (values
          (or/c (cons/c (cons/c exact-nonnegative-integer?
                                exact-nonnegative-integer?)
                        (listof (or/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      #f)))
                #f)
          (or/c #f bytes?))]
)]{

Like @racket[regexp-match-positions], etc., but with a second result
like @racket[regexp-match/end].}

@;------------------------------------------------------------------------
@section{Regexp Splitting}

@defproc[(regexp-split [pattern (or/c string? bytes? regexp? byte-regexp?)]
                       [input (or/c string? bytes? input-port?)]
                       [start-pos exact-nonnegative-integer? 0]
                       [end-pos (or/c exact-nonnegative-integer? #f) #f]
                       [input-prefix bytes? #""])
         (if (and (or (string? pattern) (regexp? pattern))
                  (string? input))
             (cons/c string? (listof string?))
             (cons/c bytes? (listof bytes?)))]{

The complement of @racket[regexp-match*]: the result is a list of
strings (if @racket[pattern] is a string or character regexp and
@racket[input] is a string) or byte strings (otherwise) from
@racket[input] that are separated by matches to
@racket[pattern]. Adjacent matches are separated with @racket[""] or
@racket[#""]. Zero-length matches are treated the same as for
@racket[regexp-match*].

If @racket[input] contains no matches (in the range @racket[start-pos]
to @racket[end-pos]), the result is a list containing @racket[input]'s
content (from @racket[start-pos] to @racket[end-pos]) as a single
element. If a match occurs at the beginning of @racket[input] (at
@racket[start-pos]), the resulting list will start with an empty
string or byte string, and if a match occurs at the end (at
@racket[end-pos]), the list will end with an empty string or byte
string. The @racket[end-pos] argument can be @racket[#f], in which
case splitting goes to the end of @racket[input] (which corresponds to
an end-of-file if @racket[input] is an input port).

@examples[
(regexp-split #rx" +" "12  34")
(regexp-split #rx"." "12  34")
(regexp-split #rx"" "12  34")
(regexp-split #rx" *" "12  34")
(regexp-split #px"\\b" "12, 13 and 14.")
]}

@;------------------------------------------------------------------------
@section{Regexp Substitution}

@defproc[(regexp-replace [pattern (or/c string? bytes? regexp? byte-regexp?)]
                         [input (or/c string? bytes?)]
                         [insert (or/c string? bytes? 
                                       ((string?) () #:rest (listof string?) . ->* . string?)
                                       ((bytes?) () #:rest (listof bytes?) . ->* . bytes?))]
                         [input-prefix bytes? #""])
         (if (and (or (string? pattern) (regexp? pattern))
                  (string? input))
             string?
             bytes?)]{

Performs a match using @racket[pattern] on @racket[input], and then
returns a string or byte string in which the matching portion of
@racket[input] is replaced with @racket[insert].  If @racket[pattern]
matches no part of @racket[input], then @racket[input] is returned
unmodified.

The @racket[insert] argument can be either a (byte) string, or a
function that returns a (byte) string. In the latter case, the
function is applied on the list of values that @racket[regexp-match]
would return (i.e., the first argument is the complete match, and then
one argument for each parenthesized sub-expression) to obtain a
replacement (byte) string.

If @racket[pattern] is a string or character regexp and @racket[input]
is a string, then @racket[insert] must be a string or a procedure that
accept strings, and the result is a string. If @racket[pattern] is a
byte string or byte regexp, or if @racket[input] is a byte string,
then @racket[insert] as a string is converted to a byte string,
@racket[insert] as a procedure is called with a byte string, and the
result is a byte string.

If @racket[insert] contains @litchar{&}, then @litchar{&}
is replaced with the matching portion of @racket[input] before it is
substituted into the match's place.  If @racket[insert] contains
@litchar{\}@nonterm{n} for some integer @nonterm{n}, then it is
replaced with the @nonterm{n}th matching sub-expression from
@racket[input]. A @litchar{&} and @litchar{\0} are aliases. If
the @nonterm{n}th sub-expression was not used in the match, or if
@nonterm{n} is greater than the number of sub-expressions in
@racket[pattern], then @litchar{\}@nonterm{n} is replaced with the
empty string.

To substitute a literal @litchar{&} or @litchar{\}, use
@litchar{\&} and @litchar{\\}, respectively, in
@racket[insert]. A @litchar{\$} in @racket[insert] is
equivalent to an empty sequence; this can be used to terminate a
number @nonterm{n} following @litchar{\}. If a @litchar{\} in
@racket[insert] is followed by anything other than a digit,
@litchar{&}, @litchar{\}, or @litchar{$}, then the @litchar{\}
by itself is treated as @litchar{\0}.

Note that the @litchar{\} described in the previous paragraphs is a
character or byte of @racket[input]. To write such an @racket[input]
as a Racket string literal, an escaping @litchar{\} is needed
before the @litchar{\}. For example, the Racket constant
@racket["\\1"] is @litchar{\1}.

@examples[
(regexp-replace "mi" "mi casa" "su")
(regexp-replace "mi" "mi casa" string-upcase)
(regexp-replace "([Mm])i ([a-zA-Z]*)" "Mi Casa" "\\1y \\2")
(regexp-replace "([Mm])i ([a-zA-Z]*)" "mi cerveza Mi Mi Mi"
                "\\1y \\2")
(regexp-replace #rx"x" "12x4x6" "\\\\")
(display (regexp-replace #rx"x" "12x4x6" "\\\\"))
]}

@defproc[(regexp-replace* [pattern (or/c string? bytes? regexp? byte-regexp?)]
                          [input (or/c string? bytes?)]
                          [insert (or/c string? bytes? 
                                        ((string?) () #:rest (listof string?) . ->* . string?)
                                        ((bytes?) () #:rest (listof bytes?) . ->* . bytes?))]
                          [input-prefix bytes? #""])
         (or/c string? bytes?)]{

Like @racket[regexp-replace], except that every instance of
@racket[pattern] in @racket[input] is replaced with @racket[insert],
instead of just the first match. Only non-overlapping instances of
@racket[pattern] in @racket[input] are replaced, so instances of
@racket[pattern] within inserted strings are @italic{not} replaced
recursively. Zero-length matches are treated the same as in
@racket[regexp-match*].

@examples[
(regexp-replace* "([Mm])i ([a-zA-Z]*)" "mi cerveza Mi Mi Mi" 
                 "\\1y \\2")
(regexp-replace* "([Mm])i ([a-zA-Z]*)" "mi cerveza Mi Mi Mi" 
                 (lambda (all one two)
                   (string-append (string-downcase one) "y"
                                  (string-upcase two))))
(display (regexp-replace* #rx"x" "12x4x6" "\\\\"))
]}

@defproc*[([(regexp-replace-quote [str string?]) string?]
           [(regexp-replace-quote [bstr bytes?]) bytes?])]{

Produces a string suitable for use as the third argument to
@racket[regexp-replace] to insert the literal sequence of characters
in @racket[str] or bytes in @racket[bstr] as a replacement.
Concretely, every @litchar{\} and @litchar{&} in @racket[str] or
@racket[bstr] is protected by a quoting @litchar{\}.

@examples[
(regexp-replace "UT" "Go UT!" "A&M")
(regexp-replace "UT" "Go UT!" (regexp-replace-quote "A&M"))
]}

