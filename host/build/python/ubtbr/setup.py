from setuptools import setup

setup(
	name="ubtbr",
	version='1.0',
	package_dir = { '': '/home/bwb/Nextcloud/research/projects/active-projects/bluetooth-parser/artifacts/ubertooth-2020/ubertooth-2020-12-R1/ubertooth-2020-12-R1/host/python/ubtbr' },
	packages=['ubtbr'],
	description="Ubtbr firmware control library",
	install_requires=['libusb1'],
	url="https://github.com/greatscottgadgets/ubertooth/",
	author="Etienne Helluy-Lafont, Univ. Lille, CNRS",
	python_requires='>=3',
	classifiers=[
		'Development Status :: 5 - Beta',
		'Intended Audience :: Developers',
		'License :: OSI Approved :: GNU General Public License (GPL)',
		'Programming Language :: Python',
		'Operating System :: OS Independent',
	],
)
