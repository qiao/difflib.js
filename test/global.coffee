{getCloseMatches, _countLeading} = require '..'

suite 'global'

test '.getCloseMatches', ->
 getCloseMatches('appel', ['ape', 'apple', 'peach', 'puppy'])
   .should.eql ['apple', 'ape']
 
 KEYWORDS = require('coffee-script').RESERVED
 getCloseMatches('wheel', KEYWORDS).should.eql ['when', 'while']
 getCloseMatches('accost', KEYWORDS).should.eql ['const']

test '._countLeading', ->
  _countLeading('   abc', ' ').should.eql 3

