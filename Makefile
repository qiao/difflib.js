TEST_TIMEOUT = 2000
TEST_REPORTER = spec

dist/difflib-browser.js: lib/difflib.js util/build.coffee
	@util/build.coffee

lib/difflib.js: src/difflib.coffee
	@coffee -c -o lib src

test: lib/difflib.js dist/difflib-browser.js
	@NODE_ENV=test \
		node_modules/.bin/mocha \
			--ui qunit \
			--require should \
			--timeout $(TEST_TIMEOUT) \
			--reporter $(TEST_REPORTER) \
			--compilers coffee:coffee-script \
			test/*.coffee

.PHONY: test
