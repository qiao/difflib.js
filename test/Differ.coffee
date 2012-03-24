{SequenceMatcher, Differ} = require '..'

suite 'Differ'

test '#_qformat', ->
  d = new Differ
  results = d._qformat('\tabcDefghiJkl\n', '\tabcdefGhijkl\n',
                       '  ^ ^  ^      ',   '  ^ ^  ^      ')
  results.should.eql [
    '- \tabcDefghiJkl\n',
    '? \t ^ ^  ^\n',
    '+ \tabcdefGhijkl\n',
    '? \t ^ ^  ^\n'
  ]

test '#_fancyReplace', ->
  d = new Differ
  d._fancyReplace(['abcDefghiJkl\n'], 0, 1,
                  ['abcdefGhijkl\n'], 0, 1).should.eql [
    '- abcDefghiJkl\n',
    '?    ^  ^  ^\n',
    '+ abcdefGhijkl\n',
    '?    ^  ^  ^\n'
  ]

test '#compare', ->
  s = new Differ
  s.compare(['one\n', 'two\n', 'three\n'],
            ['ore\n', 'tree\n', 'emu\n']).should.eql [
    '- one\n',
    '?  ^\n',
    '+ ore\n',
    '?  ^\n',
    '- two\n',
    '- three\n',
    '?  -\n',
    '+ tree\n',
    '+ emu\n'
  ]
