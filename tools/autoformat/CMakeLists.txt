
add_library(autoformat MODULE AutoFormatPass.cpp)
# Allow undefined symbols in shared objects on Darwin (this is the default behaviour on Linux)
target_link_libraries(autoformat "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")

add_library(autoformat_external STATIC autoformat.cpp)