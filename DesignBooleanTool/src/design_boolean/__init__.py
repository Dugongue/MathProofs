"""Proof-guided design recognition with checkable reconstruction certificates."""
from .core import (recognize, verify_certificate, RecognitionResult,
                   CertificateVerification, IncidenceMatrix)
from .boolean import BooleanFunction
__version__ = "0.2.0"
__all__ = ["recognize", "verify_certificate", "RecognitionResult",
           "CertificateVerification", "IncidenceMatrix", "BooleanFunction"]
