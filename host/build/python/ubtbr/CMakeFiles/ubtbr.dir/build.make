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

# Utility rule file for ubtbr.

# Include the progress variables for this target.
include python/ubtbr/CMakeFiles/ubtbr.dir/progress.make

python/ubtbr/CMakeFiles/ubtbr: python/ubtbr/build/timestamp


python/ubtbr/build/timestamp: ../python/ubtbr/ubtbr/__init__.py
python/ubtbr/build/timestamp: ../python/ubtbr/ubtbr/btctl.py
python/ubtbr/build/timestamp: ../python/ubtbr/ubtbr/lmp.py
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Generating build/timestamp"
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr && /usr/bin/python3 setup.py build
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr && /usr/bin/cmake -E touch /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr/build/timestamp

ubtbr: python/ubtbr/CMakeFiles/ubtbr
ubtbr: python/ubtbr/build/timestamp
ubtbr: python/ubtbr/CMakeFiles/ubtbr.dir/build.make

.PHONY : ubtbr

# Rule to build all files generated by this target.
python/ubtbr/CMakeFiles/ubtbr.dir/build: ubtbr

.PHONY : python/ubtbr/CMakeFiles/ubtbr.dir/build

python/ubtbr/CMakeFiles/ubtbr.dir/clean:
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr && $(CMAKE_COMMAND) -P CMakeFiles/ubtbr.dir/cmake_clean.cmake
.PHONY : python/ubtbr/CMakeFiles/ubtbr.dir/clean

python/ubtbr/CMakeFiles/ubtbr.dir/depend:
	cd /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/python/ubtbr /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr /home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/build/python/ubtbr/CMakeFiles/ubtbr.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : python/ubtbr/CMakeFiles/ubtbr.dir/depend
