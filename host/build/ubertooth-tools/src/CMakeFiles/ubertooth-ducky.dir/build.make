# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build

# Include any dependencies generated for this target.
include ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/depend.make

# Include the progress variables for this target.
include ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/progress.make

# Include the compile flags for this target's objects.
include ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/flags.make

ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o: ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/flags.make
ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o: ../ubertooth-tools/src/ubertooth-ducky.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o"
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o   -c /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/ubertooth-tools/src/ubertooth-ducky.c

ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.i"
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/ubertooth-tools/src/ubertooth-ducky.c > CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.i

ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.s"
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/ubertooth-tools/src/ubertooth-ducky.c -o CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.s

# Object files for target ubertooth-ducky
ubertooth__ducky_OBJECTS = \
"CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o"

# External object files for target ubertooth-ducky
ubertooth__ducky_EXTERNAL_OBJECTS =

ubertooth-tools/src/ubertooth-ducky: ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/ubertooth-ducky.c.o
ubertooth-tools/src/ubertooth-ducky: ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/build.make
ubertooth-tools/src/ubertooth-ducky: libubertooth/src/libubertooth.so.1.1
ubertooth-tools/src/ubertooth-ducky: /usr/lib/x86_64-linux-gnu/libusb-1.0.so
ubertooth-tools/src/ubertooth-ducky: /usr/local/lib/libbtbb.so
ubertooth-tools/src/ubertooth-ducky: /usr/lib/x86_64-linux-gnu/libbluetooth.so
ubertooth-tools/src/ubertooth-ducky: ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable ubertooth-ducky"
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/ubertooth-ducky.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/build: ubertooth-tools/src/ubertooth-ducky

.PHONY : ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/build

ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/clean:
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src && $(CMAKE_COMMAND) -P CMakeFiles/ubertooth-ducky.dir/cmake_clean.cmake
.PHONY : ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/clean

ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/depend:
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/ubertooth-tools/src /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : ubertooth-tools/src/CMakeFiles/ubertooth-ducky.dir/depend

