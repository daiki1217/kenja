from __future__ import absolute_import
import os

def is_method_body(path):
    if os.path.basename(path) != 'body':
        return False
    dirname = os.path.basename(os.path.dirname(os.path.dirname(path)))
    return dirname == '[MT]'

def is_method_parameters(path):
    if os.path.basename(path) != 'parameters':
        return False
    dirname = os.path.basename(os.path.dirname(os.path.dirname(path)))
    return dirname == '[MT]'

def get_class(path):
    split_path = path.split('/')
    cn_index = split_path.index('[CN]')
    assert cn_index +1 <= len(split_path)
    return split_path[cn_index + 1]

def get_method(path):
    split_path = path.split('/')
    mt_index = split_path.index('[MT]')
    assert mt_index +1 <= len(split_path)
    return split_path[mt_index + 1]

