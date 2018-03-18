cmake_minimum_required(VERSION 3.1)
project(sortC)

set(CMAKE_C_STANDARD 11)

set(CMAKE_C_FLAGS "-Wall -Wextra -Werror -Wshadow -pedantic -O3")

add_executable(Sort sort.c)
target_link_libraries(Sort rt pthread)

install(TARGETS DESTINATION .)
