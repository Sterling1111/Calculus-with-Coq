src/simplex_plugin_MLPACK_DEPENDENCIES:=src/simplex_main src/g_simplex
src/simplex_main.cmx : FOR_PACK=-for-pack Simplex_plugin
src/g_simplex.cmx : FOR_PACK=-for-pack Simplex_plugin
src/simplex_plugin.cmo:$(addsuffix .cmo,$(src/simplex_plugin_MLPACK_DEPENDENCIES))
src/simplex_plugin.cmx:$(addsuffix .cmx,$(src/simplex_plugin_MLPACK_DEPENDENCIES))
