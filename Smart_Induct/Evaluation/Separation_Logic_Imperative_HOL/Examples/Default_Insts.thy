theory Default_Insts
imports Main
begin

  instantiation nat :: default begin
    definition "default = (0::nat)"
    instance ..
  end

  instantiation int :: default begin
    definition "default = (0::int)"
    instance ..
  end

  instantiation bool :: default begin
    definition "default = False"
    instance ..
  end

  instantiation prod :: (default,default) default begin
    definition "default = (default,default)"
    instance ..
  end

  instantiation list :: (type)default begin
    definition "default = []"
    instance ..
  end

  instantiation option :: (type)default begin
    definition "default = None"
    instance ..
  end

  instantiation sum :: (default,type)default begin
    definition "default = Inl default"
    instance ..
  end
end
