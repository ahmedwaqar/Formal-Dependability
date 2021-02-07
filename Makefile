clean:
	find . ! -name '*Script.sml' ! -name 'Makefile' ! -name 'README.md' ! -name 'auto_smart_grid.ml' -maxdepth 1 -type f -delete
