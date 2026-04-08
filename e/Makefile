all:
	tree -H '.' -L 1 --noreport --dirsfirst -T 'Downloads' -s -D --charset utf-8 -I "index.html" | grep -v Makefile | grep -v '>[.]<' > index.html
