.. hazmat::

CommonCrypto Binding
====================

.. currentmodule:: cryptography.hazmat.bindings.commoncrypto.binding

These are `CFFI`_ bindings to the `CommonCrypto`_ C library. It is available on
Mac OS X.

.. class:: cryptography.hazmat.bindings.commoncrypto.binding.Binding()

    This is the exposed API for the CommonCrypto bindings. It has two public
    attributes:

    .. attribute:: ffi

        This is a :class:`cffi.FFI` instance. It can be used to allocate and
        otherwise manipulate CommonCrypto structures.

    .. attribute:: lib

        This is a ``cffi`` library. It can be used to call CommonCrypto
        functions, and access constants.


.. _`CFFI`: https://cffi.readthedocs.org/
.. _`CommonCrypto`: https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/Common%20Crypto.3cc.html#//apple_ref/doc/man/3cc/CommonCrypto