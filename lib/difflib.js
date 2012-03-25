
/*
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
*/

(function() {
  var Differ, Heap, IS_CHARACTER_JUNK, IS_LINE_JUNK, SequenceMatcher, arrayCmp, assert, calculateRatio, contextDiff, exports, floor, getCloseMatches, log, max, min, ndiff, unifiedDiff, _countLeading, _formatRangeContext, _formatRangeUnified,
    __indexOf = Array.prototype.indexOf || function(item) { for (var i = 0, l = this.length; i < l; i++) { if (i in this && this[i] === item) return i; } return -1; };

  floor = Math.floor, max = Math.max, min = Math.min;

  Heap = require('heap').Heap;

  assert = require('assert');

  log = console.log.bind(console);

  calculateRatio = function(matches, length) {
    if (length) {
      return 2.0 * matches / length;
    } else {
      return 1.0;
    }
  };

  arrayCmp = function(a, b) {
    var i, _ref;
    for (i = 0, _ref = max(a.length, b.length); 0 <= _ref ? i < _ref : i > _ref; 0 <= _ref ? i++ : i--) {
      if (a[i] < b[i]) return -1;
      if (a[i] > b[i]) return 1;
    }
    return 0;
  };

  SequenceMatcher = (function() {

    function SequenceMatcher(isjunk, a, b, autojunk) {
      this.isjunk = isjunk;
      if (a == null) a = '';
      if (b == null) b = '';
      this.autojunk = autojunk != null ? autojunk : true;
      this.a = this.b = null;
      this.setSeqs(a, b);
    }

    /* 
    Set the two sequences to be compared.
    */

    SequenceMatcher.prototype.setSeqs = function(a, b) {
      this.setSeq1(a);
      return this.setSeq2(b);
    };

    /* 
    Set the first sequence to be compared. 
    The second sequence to be compared is not changed.
    */

    SequenceMatcher.prototype.setSeq1 = function(a) {
      if (a === this.a) return;
      this.a = a;
      return this.matchingBlocks = this.opcodes = null;
    };

    /*
      Set the second sequence to be compared. 
      The first sequence to be compared is not changed.
    */

    SequenceMatcher.prototype.setSeq2 = function(b) {
      if (b === this.b) return;
      this.b = b;
      this.matchingBlocks = this.opcodes = null;
      this.fullbcount = null;
      return this._chainB();
    };

    SequenceMatcher.prototype._chainB = function() {
      var b, b2j, elt, i, idxs, indices, isjunk, junk, n, ntest, popular, _i, _len, _len2, _ref;
      b = this.b;
      this.b2j = b2j = {};
      for (i = 0, _len = b.length; i < _len; i++) {
        elt = b[i];
        indices = elt in b2j ? b2j[elt] : b2j[elt] = [];
        indices.push(i);
      }
      junk = {};
      isjunk = this.isjunk;
      if (isjunk) {
        _ref = Object.keys(b2j);
        for (_i = 0, _len2 = _ref.length; _i < _len2; _i++) {
          elt = _ref[_i];
          if (isjunk(elt)) {
            junk[elt] = true;
            delete b2j[elt];
          }
        }
      }
      popular = {};
      n = b.length;
      if (this.autojunk && n >= 200) {
        ntest = floor(n / 100) + 1;
        for (elt in b2j) {
          idxs = b2j[elt];
          if (idxs.length > ntest) {
            popular[elt] = true;
            delete b2j[elt];
          }
        }
      }
      this.isbjunk = function(b) {
        return b in junk;
      };
      return this.isbpopular = function(b) {
        return b in popular;
      };
    };

    /* 
    Find longest matching block in a[alo:ahi] and b[blo:bhi].
    */

    SequenceMatcher.prototype.findLongestMatch = function(alo, ahi, blo, bhi) {
      var a, b, b2j, besti, bestj, bestsize, i, isbjunk, j, j2len, k, newj2len, _i, _len, _ref, _ref2, _ref3, _ref4, _ref5, _ref6;
      _ref = [this.a, this.b, this.b2j, this.isbjunk], a = _ref[0], b = _ref[1], b2j = _ref[2], isbjunk = _ref[3];
      _ref2 = [alo, blo, 0], besti = _ref2[0], bestj = _ref2[1], bestsize = _ref2[2];
      j2len = {};
      for (i = alo; alo <= ahi ? i < ahi : i > ahi; alo <= ahi ? i++ : i--) {
        newj2len = {};
        _ref3 = (a[i] in b2j ? b2j[a[i]] : []);
        for (_i = 0, _len = _ref3.length; _i < _len; _i++) {
          j = _ref3[_i];
          if (j < blo) continue;
          if (j >= bhi) break;
          k = newj2len[j] = (j2len[j - 1] || 0) + 1;
          if (k > bestsize) {
            _ref4 = [i - k + 1, j - k + 1, k], besti = _ref4[0], bestj = _ref4[1], bestsize = _ref4[2];
          }
        }
        j2len = newj2len;
      }
      while (besti > alo && bestj > blo && !isbjunk(b[bestj - 1]) && a[besti - 1] === b[bestj - 1]) {
        _ref5 = [besti - 1, bestj - 1, bestsize + 1], besti = _ref5[0], bestj = _ref5[1], bestsize = _ref5[2];
      }
      while (besti + bestsize < ahi && bestj + bestsize < bhi && !isbjunk(b[bestj + bestsize]) && a[besti + bestsize] === b[bestj + bestsize]) {
        bestsize++;
      }
      while (besti > alo && bestj > blo && isbjunk(b[bestj - 1]) && a[besti - 1] === b[bestj - 1]) {
        _ref6 = [besti - 1, bestj - 1, bestsize + 1], besti = _ref6[0], bestj = _ref6[1], bestsize = _ref6[2];
      }
      while (besti + bestsize < ahi && bestj + bestsize < bhi && isbjunk(b[bestj + bestsize]) && a[besti + bestsize] === b[bestj + bestsize]) {
        bestsize++;
      }
      return [besti, bestj, bestsize];
    };

    /*
      Return list of matches describing matching subsequences.
    */

    SequenceMatcher.prototype.getMatchingBlocks = function() {
      var ahi, alo, bhi, blo, i, i1, i2, j, j1, j2, k, k1, k2, la, lb, matchingBlocks, nonAdjacent, queue, x, _i, _len, _ref, _ref2, _ref3, _ref4, _ref5;
      if (this.matchingBlocks) return this.matchingBlocks;
      _ref = [this.a.length, this.b.length], la = _ref[0], lb = _ref[1];
      queue = [[0, la, 0, lb]];
      matchingBlocks = [];
      while (queue.length) {
        _ref2 = queue.pop(), alo = _ref2[0], ahi = _ref2[1], blo = _ref2[2], bhi = _ref2[3];
        _ref3 = x = this.findLongestMatch(alo, ahi, blo, bhi), i = _ref3[0], j = _ref3[1], k = _ref3[2];
        if (k) {
          matchingBlocks.push(x);
          if (alo < i && blo < j) queue.push([alo, i, blo, j]);
          if (i + k < ahi && j + k < bhi) queue.push([i + k, ahi, j + k, bhi]);
        }
      }
      matchingBlocks.sort(arrayCmp);
      i1 = j1 = k1 = 0;
      nonAdjacent = [];
      for (_i = 0, _len = matchingBlocks.length; _i < _len; _i++) {
        _ref4 = matchingBlocks[_i], i2 = _ref4[0], j2 = _ref4[1], k2 = _ref4[2];
        if (i1 + k1 === i2 && j1 + k1 === j2) {
          k1 += k2;
        } else {
          if (k1) nonAdjacent.push([i1, j1, k1]);
          _ref5 = [i2, j2, k2], i1 = _ref5[0], j1 = _ref5[1], k1 = _ref5[2];
        }
      }
      if (k1) nonAdjacent.push([i1, j1, k1]);
      nonAdjacent.push([la, lb, 0]);
      return this.matchingBlocks = nonAdjacent;
    };

    /* 
    Return list of 5-tuples describing how to turn a into b
    */

    SequenceMatcher.prototype.getOpcodes = function() {
      var ai, answer, bj, i, j, size, tag, _i, _len, _ref, _ref2, _ref3;
      if (this.opcodes) return this.opcodes;
      i = j = 0;
      this.opcodes = answer = [];
      _ref = this.getMatchingBlocks();
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        _ref2 = _ref[_i], ai = _ref2[0], bj = _ref2[1], size = _ref2[2];
        tag = '';
        if (i < ai && j < bj) {
          tag = 'replace';
        } else if (i < ai) {
          tag = 'delete';
        } else if (j < bj) {
          tag = 'insert';
        }
        if (tag) answer.push([tag, i, ai, j, bj]);
        _ref3 = [ai + size, bj + size], i = _ref3[0], j = _ref3[1];
        if (size) answer.push(['equal', ai, i, bj, j]);
      }
      return answer;
    };

    /* 
    Isolate change clusters by eliminating ranges with no changes.
    XXX: not match
    */

    SequenceMatcher.prototype.getGroupedOpcodes = function(n) {
      var codes, group, groups, i1, i2, j1, j2, nn, tag, _i, _len, _ref, _ref2, _ref3, _ref4;
      if (n == null) n = 3;
      codes = this.getOpcodes();
      if (!codes.length) codes = [['equal', 0, 1, 0, 1]];
      if (codes[0][0] === 'equal') {
        _ref = codes[0], tag = _ref[0], i1 = _ref[1], i2 = _ref[2], j1 = _ref[3], j2 = _ref[4];
        codes[0] = [tag, max(i1, i2 - n), i2, max(j1, j2 - n), j2];
      }
      if (codes[codes.length - 1][0] === 'equal') {
        _ref2 = codes[codes.length - 1], tag = _ref2[0], i1 = _ref2[1], i2 = _ref2[2], j1 = _ref2[3], j2 = _ref2[4];
        codes[codes.length - 1] = [tag, i1, min(i2, i1 + n), j1, min(j2, j1 + n)];
      }
      nn = n + n;
      groups = [];
      group = [];
      for (_i = 0, _len = codes.length; _i < _len; _i++) {
        _ref3 = codes[_i], tag = _ref3[0], i1 = _ref3[1], i2 = _ref3[2], j1 = _ref3[3], j2 = _ref3[4];
        if (tag === 'equal' && i2 - i1 > nn) {
          group.push([tag, i1, min(i2, i1 + n), j1, min(j2, j1 + n)]);
          groups.push(group);
          group = [];
          _ref4 = [max(i1, i2 - n), max(j1, j2 - n)], i1 = _ref4[0], j1 = _ref4[1];
        }
        group.push([tag, i1, i2, j1, j2]);
      }
      if (group.length && !(group.length === 1 && group[0][0] === 'equal')) {
        groups.push(group);
      }
      return groups;
    };

    SequenceMatcher.prototype.ratio = function() {
      var matches;
      matches = this.getMatchingBlocks().reduce((function(sum, match) {
        return sum += match[2];
      }), 0);
      return calculateRatio(matches, this.a.length + this.b.length);
    };

    SequenceMatcher.prototype.quickRatio = function() {
      var avail, elt, fullbcount, matches, numb, _i, _j, _len, _len2, _ref, _ref2;
      if (!this.fullbcount) {
        this.fullbcount = fullbcount = {};
        _ref = this.b;
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          elt = _ref[_i];
          fullbcount[elt] = (fullbcount[elt] || 0) + 1;
        }
      }
      fullbcount = this.fullbcount;
      avail = {};
      matches = 0;
      _ref2 = this.a;
      for (_j = 0, _len2 = _ref2.length; _j < _len2; _j++) {
        elt = _ref2[_j];
        if (elt in avail) {
          numb = avail[elt];
        } else {
          numb = fullbcount[elt] || 0;
        }
        avail[elt] = numb - 1;
        if (numb > 0) matches++;
      }
      return calculateRatio(matches, this.a.length + this.b.length);
    };

    SequenceMatcher.prototype.realQuickRatio = function() {
      var la, lb, _ref;
      _ref = [this.a.length, this.b.length], la = _ref[0], lb = _ref[1];
      return calculateRatio(min(la, lb), la + lb);
    };

    return SequenceMatcher;

  })();

  getCloseMatches = function(word, possibilities, n, cutoff) {
    var result, s, score, x, _i, _j, _len, _len2, _ref, _results;
    if (n == null) n = 3;
    if (cutoff == null) cutoff = 0.6;
    if (!(n > 0)) throw new Error("n must be > 0: (" + n + ")");
    if (!((0.0 <= cutoff && cutoff <= 1.0))) {
      throw new Error("cutoff must be in [0.0, 1.0]: (" + cutoff + ")");
    }
    result = [];
    s = new SequenceMatcher();
    s.setSeq2(word);
    for (_i = 0, _len = possibilities.length; _i < _len; _i++) {
      x = possibilities[_i];
      s.setSeq1(x);
      if (s.realQuickRatio() >= cutoff && s.quickRatio() >= cutoff && s.ratio() >= cutoff) {
        result.push([s.ratio(), x]);
      }
    }
    result = Heap.nlargest(n, result);
    _results = [];
    for (_j = 0, _len2 = result.length; _j < _len2; _j++) {
      _ref = result[_j], score = _ref[0], x = _ref[1];
      _results.push(x);
    }
    return _results;
  };

  /*
  Return number of `ch` characters at the start of `line`.
  */

  _countLeading = function(line, ch) {
    var i, n, _ref;
    _ref = [0, line.length], i = _ref[0], n = _ref[1];
    while (i < n && line[i] === ch) {
      i++;
    }
    return i;
  };

  Differ = (function() {

    function Differ(linejunk, charjunk) {
      this.linejunk = linejunk;
      this.charjunk = charjunk;
    }

    Differ.prototype.compare = function(a, b) {
      var ahi, alo, bhi, blo, cruncher, g, line, lines, tag, _i, _j, _len, _len2, _ref, _ref2;
      cruncher = new SequenceMatcher(this.linejunk, a, b);
      lines = [];
      _ref = cruncher.getOpcodes();
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        _ref2 = _ref[_i], tag = _ref2[0], alo = _ref2[1], ahi = _ref2[2], blo = _ref2[3], bhi = _ref2[4];
        switch (tag) {
          case 'replace':
            g = this._fancyReplace(a, alo, ahi, b, blo, bhi);
            break;
          case 'delete':
            g = this._dump('-', a, alo, ahi);
            break;
          case 'insert':
            g = this._dump('+', b, blo, bhi);
            break;
          case 'equal':
            g = this._dump(' ', a, alo, ahi);
            break;
          default:
            throw new Error("unknow tag (" + tag + ")");
        }
        for (_j = 0, _len2 = g.length; _j < _len2; _j++) {
          line = g[_j];
          lines.push(line);
        }
      }
      return lines;
    };

    Differ.prototype._dump = function(tag, x, lo, hi) {
      var i, _results;
      _results = [];
      for (i = lo; lo <= hi ? i < hi : i > hi; lo <= hi ? i++ : i--) {
        _results.push("" + tag + " " + x[i]);
      }
      return _results;
    };

    Differ.prototype._plainReplace = function(a, alo, ahi, b, blo, bhi) {
      var first, g, line, lines, second, _i, _j, _len, _len2, _ref;
      assert(alo < ahi && blo < bhi);
      if (bhi - blo < ahi - alo) {
        first = this._dump('+', b, blo, bhi);
        second = this._dump('-', a, alo, ahi);
      } else {
        first = this._dump('-', a, alo, ahi);
        second = this._dump('+', b, blo, bhi);
      }
      lines = [];
      _ref = [first, second];
      for (_i = 0, _len = _ref.length; _i < _len; _i++) {
        g = _ref[_i];
        for (_j = 0, _len2 = g.length; _j < _len2; _j++) {
          line = g[_j];
          lines.push(line);
        }
      }
      return lines;
    };

    Differ.prototype._fancyReplace = function(a, alo, ahi, b, blo, bhi) {
      var aelt, ai, ai1, ai2, atags, belt, bestRatio, besti, bestj, bj, bj1, bj2, btags, cruncher, cutoff, eqi, eqj, i, j, la, lb, line, lines, tag, _i, _j, _k, _l, _len, _len2, _len3, _len4, _len5, _m, _ref, _ref10, _ref11, _ref12, _ref13, _ref2, _ref3, _ref4, _ref5, _ref6, _ref7, _ref8, _ref9;
      _ref = [0.74, 0.75], bestRatio = _ref[0], cutoff = _ref[1];
      cruncher = new SequenceMatcher(this.charjunk);
      _ref2 = [null, null], eqi = _ref2[0], eqj = _ref2[1];
      lines = [];
      for (j = blo; blo <= bhi ? j < bhi : j > bhi; blo <= bhi ? j++ : j--) {
        bj = b[j];
        cruncher.setSeq2(bj);
        for (i = alo; alo <= ahi ? i < ahi : i > ahi; alo <= ahi ? i++ : i--) {
          ai = a[i];
          if (ai === bj) {
            if (eqi === null) _ref3 = [i, j], eqi = _ref3[0], eqj = _ref3[1];
            continue;
          }
          cruncher.setSeq1(ai);
          if (cruncher.realQuickRatio() > bestRatio && cruncher.quickRatio() > bestRatio && cruncher.ratio() > bestRatio) {
            _ref4 = [cruncher.ratio(), i, j], bestRatio = _ref4[0], besti = _ref4[1], bestj = _ref4[2];
          }
        }
      }
      if (bestRatio < cutoff) {
        if (eqi === null) {
          _ref5 = this._plainReplace(a, alo, ahi, b, blo, bhi);
          for (_i = 0, _len = _ref5.length; _i < _len; _i++) {
            line = _ref5[_i];
            lines.push(line);
          }
          return lines;
        }
        _ref6 = [eqi, eqj, 1.0], besti = _ref6[0], bestj = _ref6[1], bestRatio = _ref6[2];
      } else {
        eqi = null;
      }
      _ref7 = this._fancyHelper(a, alo, besti, b, blo, bestj);
      for (_j = 0, _len2 = _ref7.length; _j < _len2; _j++) {
        line = _ref7[_j];
        lines.push(line);
      }
      _ref8 = [a[besti], b[bestj]], aelt = _ref8[0], belt = _ref8[1];
      if (eqi === null) {
        atags = btags = '';
        cruncher.setSeqs(aelt, belt);
        _ref9 = cruncher.getOpcodes();
        for (_k = 0, _len3 = _ref9.length; _k < _len3; _k++) {
          _ref10 = _ref9[_k], tag = _ref10[0], ai1 = _ref10[1], ai2 = _ref10[2], bj1 = _ref10[3], bj2 = _ref10[4];
          _ref11 = [ai2 - ai1, bj2 - bj1], la = _ref11[0], lb = _ref11[1];
          switch (tag) {
            case 'replace':
              atags += Array(la + 1).join('^');
              btags += Array(lb + 1).join('^');
              break;
            case 'delete':
              atags += Array(la + 1).join('-');
              break;
            case 'insert':
              btags += Array(lb + 1).join('+');
              break;
            case 'equal':
              atags += Array(la + 1).join(' ');
              btags += Array(lb + 1).join(' ');
              break;
            default:
              throw new Error("unknow tag (" + tag + ")");
          }
        }
        _ref12 = this._qformat(aelt, belt, atags, btags);
        for (_l = 0, _len4 = _ref12.length; _l < _len4; _l++) {
          line = _ref12[_l];
          lines.push(line);
        }
      } else {
        lines.push('  ' + aelt);
      }
      _ref13 = this._fancyHelper(a, besti + 1, ahi, b, bestj + 1, bhi);
      for (_m = 0, _len5 = _ref13.length; _m < _len5; _m++) {
        line = _ref13[_m];
        lines.push(line);
      }
      return lines;
    };

    Differ.prototype._fancyHelper = function(a, alo, ahi, b, blo, bhi) {
      var g;
      g = [];
      if (alo < ahi) {
        if (blo < bhi) {
          g = this._fancyReplace(a, alo, ahi, b, blo, bhi);
        } else {
          g = this._dump('-', a, alo, ahi);
        }
      } else if (blo < bhi) {
        g = this._dump('+', b, blo, bhi);
      }
      return g;
    };

    Differ.prototype._qformat = function(aline, bline, atags, btags) {
      var common, lines;
      lines = [];
      common = min(_countLeading(aline, '\t'), _countLeading(bline, '\t'));
      common = min(common, _countLeading(atags.slice(0, common), ' '));
      common = min(common, _countLeading(btags.slice(0, common), ' '));
      atags = atags.slice(common).trimRight();
      btags = btags.slice(common).trimRight();
      lines.push('- ' + aline);
      if (atags.length) {
        lines.push("? " + (Array(common + 1).join('\t')) + atags + "\n");
      }
      lines.push('+ ' + bline);
      if (btags.length) {
        lines.push("? " + (Array(common + 1).join('\t')) + btags + "\n");
      }
      return lines;
    };

    return Differ;

  })();

  IS_LINE_JUNK = function(line, pat) {
    if (pat == null) pat = /^\s*#?\s*$/;
    return pat.test(line);
  };

  IS_CHARACTER_JUNK = function(ch, ws) {
    if (ws == null) ws = ' \t';
    return __indexOf.call(ws, ch) >= 0;
  };

  _formatRangeUnified = function(start, stop) {
    var beginning, length;
    beginning = start + 1;
    length = stop - start;
    if (length === 1) return "" + beginning;
    if (!length) beginning--;
    return "" + beginning + "," + length;
  };

  unifiedDiff = function(a, b, _arg) {
    var file1Range, file2Range, first, fromdate, fromfile, fromfiledate, group, i1, i2, j1, j2, last, line, lines, lineterm, n, started, tag, todate, tofile, tofiledate, _i, _j, _k, _l, _len, _len2, _len3, _len4, _len5, _m, _ref, _ref2, _ref3, _ref4, _ref5, _ref6;
    fromfile = _arg.fromfile, tofile = _arg.tofile, fromfiledate = _arg.fromfiledate, tofiledate = _arg.tofiledate, n = _arg.n, lineterm = _arg.lineterm;
    if (fromfile == null) fromfile = '';
    if (tofile == null) tofile = '';
    if (fromfiledate == null) fromfiledate = '';
    if (tofiledate == null) tofiledate = '';
    if (n == null) n = 3;
    if (lineterm == null) lineterm = '\n';
    lines = [];
    started = false;
    _ref = (new SequenceMatcher(null, a, b)).getGroupedOpcodes();
    for (_i = 0, _len = _ref.length; _i < _len; _i++) {
      group = _ref[_i];
      if (!started) {
        started = true;
        fromdate = fromfiledate ? "\t" + fromfiledate : '';
        todate = tofiledate ? "\t" + tofiledate : '';
        lines.push("--- " + fromfile + fromdate + lineterm);
        lines.push("+++ " + tofile + todate + lineterm);
      }
      _ref2 = [group[0], group[group.length - 1]], first = _ref2[0], last = _ref2[1];
      file1Range = _formatRangeUnified(first[1], last[2]);
      file2Range = _formatRangeUnified(first[3], last[4]);
      lines.push("@@ -" + file1Range + " +" + file2Range + " @@" + lineterm);
      for (_j = 0, _len2 = group.length; _j < _len2; _j++) {
        _ref3 = group[_j], tag = _ref3[0], i1 = _ref3[1], i2 = _ref3[2], j1 = _ref3[3], j2 = _ref3[4];
        if (tag === 'equal') {
          _ref4 = a.slice(i1, i2);
          for (_k = 0, _len3 = _ref4.length; _k < _len3; _k++) {
            line = _ref4[_k];
            lines.push(' ' + line);
          }
          continue;
        }
        if (tag === 'replace' || tag === 'delete') {
          _ref5 = a.slice(i1, i2);
          for (_l = 0, _len4 = _ref5.length; _l < _len4; _l++) {
            line = _ref5[_l];
            lines.push('-' + line);
          }
        }
        if (tag === 'replace' || tag === 'insert') {
          _ref6 = b.slice(j1, j2);
          for (_m = 0, _len5 = _ref6.length; _m < _len5; _m++) {
            line = _ref6[_m];
            lines.push('+' + line);
          }
        }
      }
    }
    return lines;
  };

  _formatRangeContext = function(start, stop) {
    var beginning, length;
    beginning = start + 1;
    length = stop - start;
    if (!length) beginning--;
    if (length <= 1) return "" + beginning;
    return "" + beginning + "," + (beginning + length - 1);
  };

  contextDiff = function(a, b, _arg) {
    var file1Range, file2Range, first, fromdate, fromfile, fromfiledate, group, i1, i2, j1, j2, last, line, lines, lineterm, n, prefix, started, tag, todate, tofile, tofiledate, _, _i, _j, _k, _l, _len, _len2, _len3, _len4, _len5, _m, _ref, _ref2, _ref3, _ref4, _ref5, _ref6;
    fromfile = _arg.fromfile, tofile = _arg.tofile, fromfiledate = _arg.fromfiledate, tofiledate = _arg.tofiledate, n = _arg.n, lineterm = _arg.lineterm;
    if (fromfile == null) fromfile = '';
    if (tofile == null) tofile = '';
    if (fromfiledate == null) fromfiledate = '';
    if (tofiledate == null) tofiledate = '';
    if (n == null) n = 3;
    if (lineterm == null) lineterm = '\n';
    prefix = {
      insert: '+ ',
      "delete": '- ',
      replace: '! ',
      equal: '  '
    };
    started = false;
    lines = [];
    _ref = (new SequenceMatcher(null, a, b)).getGroupedOpcodes();
    for (_i = 0, _len = _ref.length; _i < _len; _i++) {
      group = _ref[_i];
      if (!started) {
        started = true;
        fromdate = fromfiledate ? "\t" + fromfiledate : '';
        todate = tofiledate ? "\t" + tofiledate : '';
        lines.push("*** " + fromfile + fromdate + lineterm);
        lines.push("--- " + tofile + todate + lineterm);
        _ref2 = [group[0], group[group.length - 1]], first = _ref2[0], last = _ref2[1];
        lines.push('***************' + lineterm);
        file1Range = _formatRangeContext(first[1], last[2]);
        lines.push("*** " + file1Range + " ****" + lineterm);
        if (((function() {
          var _j, _len2, _ref3, _results;
          _results = [];
          for (_j = 0, _len2 = group.length; _j < _len2; _j++) {
            _ref3 = group[_j], tag = _ref3[0], _ = _ref3[1], _ = _ref3[2], _ = _ref3[3], _ = _ref3[4];
            _results.push(tag === 'replace' || tag === 'delete');
          }
          return _results;
        })()).some(function(x) {
          return x;
        })) {
          for (_j = 0, _len2 = group.length; _j < _len2; _j++) {
            _ref3 = group[_j], tag = _ref3[0], i1 = _ref3[1], i2 = _ref3[2], _ = _ref3[3], _ = _ref3[4];
            if (tag !== 'insert') {
              _ref4 = a.slice(i1, i2);
              for (_k = 0, _len3 = _ref4.length; _k < _len3; _k++) {
                line = _ref4[_k];
                lines.push(prefix[tag] + line);
              }
            }
          }
        }
        file2Range = _formatRangeContext(first[3], last[4]);
        lines.push("--- " + file2Range + " ----" + lineterm);
        if (((function() {
          var _l, _len4, _ref5, _results;
          _results = [];
          for (_l = 0, _len4 = group.length; _l < _len4; _l++) {
            _ref5 = group[_l], tag = _ref5[0], _ = _ref5[1], _ = _ref5[2], _ = _ref5[3], _ = _ref5[4];
            _results.push(tag === 'replace' || tag === 'insert');
          }
          return _results;
        })()).some(function(x) {
          return x;
        })) {
          for (_l = 0, _len4 = group.length; _l < _len4; _l++) {
            _ref5 = group[_l], tag = _ref5[0], _ = _ref5[1], _ = _ref5[2], j1 = _ref5[3], j2 = _ref5[4];
            if (tag !== 'delete') {
              _ref6 = b.slice(j1, j2);
              for (_m = 0, _len5 = _ref6.length; _m < _len5; _m++) {
                line = _ref6[_m];
                lines.push(prefix[tag] + line);
              }
            }
          }
        }
      }
    }
    return lines;
  };

  ndiff = function(a, b, linejunk, charjunk) {
    if (charjunk == null) charjunk = IS_CHARACTER_JUNK;
    return (new Differ(linejunk, charjunk)).compare(a, b);
  };

  exports = (typeof module !== "undefined" && module !== null ? module.exports : void 0) || (window.difflib = {});

  exports.SequenceMatcher = SequenceMatcher;

  exports.getCloseMatches = getCloseMatches;

  exports._countLeading = _countLeading;

  exports.Differ = Differ;

  exports.IS_LINE_JUNK = IS_LINE_JUNK;

  exports.IS_CHARACTER_JUNK = IS_CHARACTER_JUNK;

  exports._formatRangeUnified = _formatRangeUnified;

  exports.unifiedDiff = unifiedDiff;

  exports._formatRangeContext = _formatRangeContext;

  exports.contextDiff = contextDiff;

  exports.ndiff = ndiff;

}).call(this);
