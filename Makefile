TEST_TIMEOUT = 2000
TEST_REPORTER = spec

lib/difflib.js: src/difflib.coffee
	@coffee -c -o lib src

test:
	@NODE_ENV=test \
		node_modules/.bin/mocha \
			--ui qunit \
			--require should \
			--timeout $(TEST_TIMEOUT) \
			--reporter $(TEST_REPORTER) 

.PHONY: test
