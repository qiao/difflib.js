###
Module difflib -- helpers for computing deltas between objects.

Function get_close_matches(word, possibilities, n=3, cutoff=0.6):
    Use SequenceMatcher to return list of the best "good enough" matches.

Function context_diff(a, b):
    For two lists of strings, return a delta in context diff format.

Function ndiff(a, b):
    Return a delta: the difference between `a` and `b` (lists of strings).

Function restore(delta, which):
    Return one of the two sequences that generated an ndiff delta.

Function unified_diff(a, b):
    For two lists of strings, return a delta in unified diff format.

Class SequenceMatcher:
    A flexible class for comparing pairs of sequences of any type.

Class Differ:
    For producing human-readable deltas from sequences of lines of text.

Class HtmlDiff:
    For producing HTML side by side comparison with change highlights.
###


{floor, max, min} = Math
{Heap} = require('heap')
assert = require('assert')
log = console.log.bind(console)

calculateRatio = (matches, length) ->
  if length then (2.0 * matches / length) else 1.0

arrayCmp = (a, b) ->
  for i in [0...max(a.length, b.length)]
    return -1 if a[i] < b[i]
    return 1 if a[i] > b[i]
  0
      

class SequenceMatcher
  constructor: (@isjunk, a='', b='', @autojunk=true) ->
    @a = @b = null
    @setSeqs(a, b)

  ### 
  Set the two sequences to be compared. 
  ###
  setSeqs: (a, b) ->
    @setSeq1(a)
    @setSeq2(b)

  ### 
  Set the first sequence to be compared. 
  The second sequence to be compared is not changed.
  ###
  setSeq1: (a) ->
    return if a is @a
    @a = a
    @matchingBlocks = @opcodes = null


  ###
  Set the second sequence to be compared. 
  The first sequence to be compared is not changed.
  ###
  setSeq2: (b) ->
    return if b is @b
    @b = b
    @matchingBlocks = @opcodes = null
    @fullbcount = null
    @_chainB()

  _chainB: ->
    b = @b
    @b2j = b2j = {}

    for elt, i in b
      indices = if elt of b2j then b2j[elt] else b2j[elt] = []
      indices.push(i)

    junk = {}
    isjunk = @isjunk
    if isjunk
      for elt in Object.keys(b2j)
        if isjunk(elt)
          junk[elt] = true
          delete b2j[elt]

    popular = {}
    n = b.length
    if @autojunk and n >= 200
      ntest = floor(n / 100) + 1
      for elt, idxs of b2j
        if idxs.length > ntest
          popular[elt] = true
          delete b2j[elt]

    @isbjunk = (b) -> b of junk
    @isbpopular = (b) -> b of popular

  ### 
  Find longest matching block in a[alo:ahi] and b[blo:bhi].  
  ###
  findLongestMatch: (alo, ahi, blo, bhi) ->
    [a, b, b2j, isbjunk] = [@a, @b, @b2j, @isbjunk]
    [besti, bestj, bestsize] = [alo, blo, 0]

    j2len = {}
    for i in [alo...ahi]
      newj2len = {}
      for j in (if a[i] of b2j then b2j[a[i]] else [])
        continue if j < blo
        break if j >= bhi
        k = newj2len[j] = (j2len[j-1] or 0) + 1
        if k > bestsize
          [besti, bestj, bestsize] = [i-k+1,j-k+1,k]
      j2len = newj2len

    while besti > alo and bestj > blo and
        not isbjunk(b[bestj-1]) and
        a[besti-1] is b[bestj-1]
      [besti, bestj, bestsize] = [besti-1, bestj-1, bestsize+1]
    while besti+bestsize < ahi and bestj+bestsize < bhi and
        not isbjunk(b[bestj+bestsize]) and
        a[besti+bestsize] is b[bestj+bestsize]
      bestsize++

    while besti > alo and bestj > blo and
        isbjunk(b[bestj-1]) and
        a[besti-1] is b[bestj-1]
      [besti,bestj,bestsize] = [besti-1, bestj-1, bestsize+1]
    while besti+bestsize < ahi and bestj+bestsize < bhi and
        isbjunk(b[bestj+bestsize]) and
        a[besti+bestsize] is b[bestj+bestsize]
      bestsize++

    [besti, bestj, bestsize]

  ###
  Return list of matches describing matching subsequences.
  ###
  getMatchingBlocks: ->
    return @matchingBlocks if @matchingBlocks
    [la, lb] = [@a.length, @b.length]

    queue = [[0, la, 0, lb]]
    matchingBlocks = []
    while queue.length
      [alo, ahi, blo, bhi] = queue.pop()
      [i, j, k] = x = @findLongestMatch(alo, ahi, blo, bhi)

      if k
        matchingBlocks.push(x)
        if alo < i and blo < j
          queue.push([alo, i, blo, j])
        if i+k < ahi and j+k < bhi
          queue.push([i+k, ahi, j+k, bhi])
    matchingBlocks.sort(arrayCmp)

    i1 = j1 = k1 = 0
    nonAdjacent = []
    for [i2, j2, k2] in matchingBlocks
      if i1 + k1 is i2 and j1 + k1 is j2
        k1 += k2
      else
        if k1
          nonAdjacent.push([i1, j1, k1])
        [i1, j1, k1] = [i2, j2, k2]
    if k1
      nonAdjacent.push([i1, j1, k1])

    nonAdjacent.push([la, lb, 0])
    @matchingBlocks = nonAdjacent

  ### 
  Return list of 5-tuples describing how to turn a into b 
  ###
  getOpcodes: ->
    return @opcodes if @opcodes
    i = j = 0
    @opcodes = answer = []
    for [ai, bj, size] in @getMatchingBlocks()
      tag = ''
      if i < ai and j < bj
        tag = 'replace'
      else if i < ai
        tag = 'delete'
      else if j < bj
        tag = 'insert'
      if tag
        answer.push([tag, i, ai, j, bj])
      [i, j] = [ai+size, bj+size]

      if size
        answer.push(['equal', ai, i, bj, j])
    answer

  ### 
  Isolate change clusters by eliminating ranges with no changes.
  XXX: not match
  ###
  getGroupedOpcodes: (n=3) ->
    codes = @getOpcodes()
    unless codes.length
      codes = [['equal', 0, 1, 0, 1]]
    if codes[0][0] is 'equal'
      [tag, i1, i2, j1, j2] = codes[0]
      codes[0] = [tag, max(i1, i2-n), i2, max(j1, j2-n), j2]
    if codes[codes.length-1][0] is 'equal'
      [tag, i1, i2, j1, j2] = codes[codes.length-1]
      codes[codes.length-1] = [tag, i1, min(i2, i1+n), j1, min(j2, j1+n)]

    nn = n + n
    groups = []
    group = []
    for [tag, i1, i2, j1, j2] in codes
      if tag is 'equal' and i2-i1 > nn
        group.push([tag, i1, min(i2, i1+n), j1, min(j2, j1+n)])
        groups.push(group)
        group = []
        [i1, j1] = [max(i1, i2-n), max(j1, j2-n)]
      group.push([tag, i1, i2, j1, j2])
    if group.length and not (group.length is 1 and group[0][0] is 'equal')
      groups.push(group)
    groups

  ratio: ->
    matches = @getMatchingBlocks().reduce ((sum, match) ->
      sum += match[2]
    ), 0
    calculateRatio(matches, @a.length + @b.length)

  quickRatio: ->
    unless @fullbcount
      @fullbcount = fullbcount = {}
      for elt in @b
        fullbcount[elt] = (fullbcount[elt] or 0) + 1

    fullbcount = @fullbcount
    avail = {}
    matches = 0
    for elt in @a
      if elt of avail
        numb = avail[elt]
      else
        numb = fullbcount[elt] or 0
      avail[elt] = numb - 1
      if numb > 0
        matches++
    calculateRatio(matches, @a.length + @b.length)

  realQuickRatio: ->
    [la, lb] = [@a.length, @b.length]
    calculateRatio(min(la, lb), la + lb)

getCloseMatches = (word, possibilities, n=3, cutoff=0.6) ->
  unless n > 0
    throw new Error("n must be > 0: (#{n})")
  unless 0.0 <= cutoff <= 1.0
    throw new Error("cutoff must be in [0.0, 1.0]: (#{cutoff})")
  result = []
  s = new SequenceMatcher()
  s.setSeq2(word)
  for x in possibilities
    s.setSeq1(x)
    if s.realQuickRatio() >= cutoff and
        s.quickRatio() >= cutoff and
        s.ratio() >= cutoff
      result.push([s.ratio(), x])

  result = Heap.nlargest(n, result)
  (x for [score, x] in result)

###
Return number of `ch` characters at the start of `line`.
###
_countLeading = (line, ch) ->
  [i, n] = [0, line.length]
  while i < n and line[i] is ch
    i++
  i


class Differ
  constructor: (@linejunk, @charjunk) ->

  compare: (a, b) ->
    cruncher = new SequenceMatcher(@linejunk, a, b)
    lines = []
    for [tag, alo, ahi, blo, bhi] in cruncher.getOpcodes()
      switch tag
        when 'replace'
          g = @_fancyReplace(a, alo, ahi, b, blo, bhi)
        when 'delete'
          g = @_dump('-', a, alo, ahi)
        when 'insert'
          g = @_dump('+', b, blo, bhi)
        when 'equal'
          g = @_dump(' ', a, alo, ahi)
        else
          throw new Error("unknow tag (#{tag})")
      lines.push(line) for line in g
    lines

  _dump: (tag, x, lo, hi) ->
    ("#{tag} #{x[i]}" for i in [lo...hi])

  _plainReplace: (a, alo, ahi, b, blo, bhi) ->
    assert(alo < ahi and blo < bhi)
    if bhi - blo < ahi - alo
      first  = @_dump('+', b, blo, bhi)
      second = @_dump('-', a, alo, ahi)
    else
      first  = @_dump('-', a, alo, ahi)
      second = @_dump('+', b, blo, bhi)

    lines = []
    lines.push(line) for line in g for g in [first, second]
    lines

  _fancyReplace: (a, alo, ahi, b, blo, bhi) ->
    [bestRatio, cutoff] = [0.74, 0.75]
    cruncher = new SequenceMatcher(@charjunk)
    [eqi, eqj] = [null, null]
    lines = []

    for j in [blo...bhi]
      bj = b[j]
      cruncher.setSeq2(bj)
      for i in [alo...ahi]
        ai = a[i]
        if ai is bj
          if eqi is null
            [eqi, eqj] = [i, j]
          continue
        cruncher.setSeq1(ai)

        if cruncher.realQuickRatio() > bestRatio and
            cruncher.quickRatio() > bestRatio and
            cruncher.ratio() > bestRatio
          [bestRatio, besti, bestj] = [cruncher.ratio(), i, j]

    if bestRatio < cutoff
      if eqi is null
        for line in @_plainReplace(a, alo, ahi, b, blo, bhi)
          lines.push(line)
        return lines
      [besti, bestj, bestRatio] = [eqi, eqj, 1.0]
    else
      eqi = null

    for line in @_fancyHelper(a, alo, besti, b, blo, bestj)
      lines.push(line)

    [aelt, belt] = [a[besti], b[bestj]]
    if eqi is null
      atags = btags = ''
      cruncher.setSeqs(aelt, belt)
      for [tag, ai1, ai2, bj1, bj2] in cruncher.getOpcodes()
        [la, lb] = [ai2 - ai1, bj2 - bj1]
        switch tag
          when 'replace'
            atags += Array(la+1).join('^')
            btags += Array(lb+1).join('^')
          when 'delete'
            atags += Array(la+1).join('-')
          when 'insert'
            btags += Array(lb+1).join('+')
          when 'equal'
            atags += Array(la+1).join(' ')
            btags += Array(lb+1).join(' ')
          else
            throw new Error("unknow tag (#{tag})")
      for line in @_qformat(aelt, belt, atags, btags)
        lines.push(line)
    else
      lines.push('  ' + aelt)

    for line in @_fancyHelper(a, besti+1, ahi, b, bestj+1, bhi)
      lines.push(line)

    lines

  _fancyHelper: (a, alo, ahi, b, blo, bhi) ->
    g = []
    if alo < ahi
      if blo < bhi
        g = @_fancyReplace(a, alo, ahi, b, blo, bhi)
      else
        g = @_dump('-', a, alo, ahi)
    else if blo < bhi
      g = @_dump('+', b, blo, bhi)
    g

  _qformat: (aline, bline, atags, btags) ->
    lines = []

    common = min(_countLeading(aline, '\t'),
                 _countLeading(bline, '\t'))
    common = min(common, _countLeading(atags[0...common], ' '))
    common = min(common, _countLeading(btags[0...common], ' '))
    atags = atags[common..].trimRight()
    btags = btags[common..].trimRight()

    lines.push('- ' + aline)
    if atags.length
      lines.push("? #{Array(common+1).join('\t')}#{atags}\n")

    lines.push('+ ' + bline)
    if btags.length
      lines.push("? #{Array(common+1).join('\t')}#{btags}\n")
    lines

IS_LINE_JUNK = (line, pat=/^\s*#?\s*$/) ->
  pat.test(line)

IS_CHARACTER_JUNK = (ch, ws=' \t') ->
  ch in ws


_formatRangeUnified = (start, stop) ->
  beginning = start + 1
  length = stop - start
  return "#{beginning}" if length is 1
  beginning-- unless length
  "#{beginning},#{length}"

unifiedDiff = (a, b, {fromfile, tofile, fromfiledate, tofiledate, n, lineterm}) ->
  fromfile     ?= ''
  tofile       ?= ''
  fromfiledate ?= ''
  tofiledate   ?= ''
  n            ?= 3
  lineterm     ?= '\n'

  lines = []
  started = false
  for group in (new SequenceMatcher(null, a, b)).getGroupedOpcodes()
    unless started
      started = true
      fromdate = if fromfiledate then "\t#{fromfiledate}" else ''
      todate = if tofiledate then "\t#{tofiledate}" else ''
      lines.push("--- #{fromfile}#{fromdate}#{lineterm}")
      lines.push("+++ #{tofile}#{todate}#{lineterm}")

    [first, last] = [group[0], group[group.length-1]]
    file1Range = _formatRangeUnified(first[1], last[2])
    file2Range = _formatRangeUnified(first[3], last[4])
    lines.push("@@ -#{file1Range} +#{file2Range} @@#{lineterm}")

    for [tag, i1, i2, j1, j2] in group
      if tag is 'equal'
        lines.push(' ' + line) for line in a[i1...i2]
        continue
      if tag in ['replace', 'delete']
        lines.push('-' + line) for line in a[i1...i2]
      if tag in ['replace', 'insert']
        lines.push('+' + line) for line in b[j1...j2]

  lines

_formatRangeContext = (start, stop) ->
  beginning = start + 1
  length = stop - start
  beginning-- unless length
  return "#{beginning}" if length <= 1
  "#{beginning},#{beginning + length - 1}"

contextDiff = (a, b, {fromfile, tofile, fromfiledate, tofiledate, n, lineterm}) ->
  fromfile     ?= ''
  tofile       ?= ''
  fromfiledate ?= ''
  tofiledate   ?= ''
  n            ?= 3
  lineterm     ?= '\n'

  prefix =
    insert  : '+ '
    delete  : '- '
    replace : '! '
    equal   : '  '
  started = false
  lines = []
  for group in (new SequenceMatcher(null, a, b)).getGroupedOpcodes()
    unless started
      started = true
      fromdate = if fromfiledate then "\t#{fromfiledate}" else ''
      todate = if tofiledate then "\t#{tofiledate}" else ''
      lines.push("*** #{fromfile}#{fromdate}#{lineterm}")
      lines.push("--- #{tofile}#{todate}#{lineterm}")

      [first, last] = [group[0], group[group.length-1]]
      lines.push('***************' + lineterm)

      file1Range = _formatRangeContext(first[1], last[2])
      lines.push("*** #{file1Range} ****#{lineterm}")

      if ((tag in ['replace', 'delete']) for [tag, _, _, _, _] in group).some((x) -> x)
        for [tag, i1, i2, _, _] in group
          if tag isnt 'insert'
            for line in a[i1...i2]
              lines.push(prefix[tag] + line)

      file2Range = _formatRangeContext(first[3], last[4])
      lines.push("--- #{file2Range} ----#{lineterm}")

      if ((tag in ['replace', 'insert']) for [tag, _, _, _, _] in group).some((x) -> x)
        for [tag, _, _, j1, j2] in group
          if tag isnt 'delete'
            for line in b[j1...j2]
              lines.push(prefix[tag] + line)

  lines

ndiff = (a, b, linejunk, charjunk=IS_CHARACTER_JUNK) ->
  (new Differ(linejunk, charjunk)).compare(a, b)

exports = module?.exports or (window.difflib = {})
exports.SequenceMatcher     = SequenceMatcher
exports.getCloseMatches     = getCloseMatches
exports._countLeading       = _countLeading
exports.Differ              = Differ
exports.IS_LINE_JUNK        = IS_LINE_JUNK
exports.IS_CHARACTER_JUNK   = IS_CHARACTER_JUNK
exports._formatRangeUnified = _formatRangeUnified
exports.unifiedDiff         = unifiedDiff
exports._formatRangeContext = _formatRangeContext
exports.contextDiff         = contextDiff
exports.ndiff               = ndiff
