"""Builds a platform wheel: pure Python plus the prebuilt libleanelpi, usable on any Python 3."""
import os

from setuptools import setup
from setuptools.dist import Distribution

try:
    from setuptools.command.bdist_wheel import bdist_wheel
except ImportError:  # setuptools < 70.1
    from wheel.bdist_wheel import bdist_wheel


class PlatformWheel(bdist_wheel):
    def finalize_options(self) -> None:
        super().finalize_options()
        self.root_is_pure = False

    def get_tag(self):
        # No compiled Python extension: the library is reached through ctypes, so one wheel
        # per platform serves every Python 3 version.
        _, _, plat = super().get_tag()
        return "py3", "none", os.environ.get("LEANELPI_WHEEL_PLAT", plat)


class BinaryDistribution(Distribution):
    def has_ext_modules(self) -> bool:
        return True


setup(distclass=BinaryDistribution, cmdclass={"bdist_wheel": PlatformWheel})
