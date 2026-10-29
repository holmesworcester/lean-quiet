// Included after lq_root is declared. PHPicker owns its presentation and grants
// access only to the chosen file. ImageIO decodes a bounded, oriented thumbnail.
#import <PhotosUI/PhotosUI.h>
#import <ImageIO/ImageIO.h>
#include "../native/photo.h"

static LqPhoto lq_photo = LQ_PHOTO_INIT;
static PHPickerViewController* lq_picker;
@interface LeanPhotoPicker : NSObject <PHPickerViewControllerDelegate>
@property(nonatomic) uint32_t token;
@end
static LeanPhotoPicker* lq_picker_delegate;

static void lq_photo_file(uint32_t token, NSURL* url) {
  if (!lq_photo_current(&lq_photo, token)) return;
  CGImageSourceRef source = url ? CGImageSourceCreateWithURL((__bridge CFURLRef)url, NULL) : NULL;
  NSDictionary* options = @{
    (__bridge NSString*)kCGImageSourceCreateThumbnailFromImageAlways: @YES,
    (__bridge NSString*)kCGImageSourceCreateThumbnailWithTransform: @YES,
    (__bridge NSString*)kCGImageSourceThumbnailMaxPixelSize: @2048,
    (__bridge NSString*)kCGImageSourceShouldCacheImmediately: @YES
  };
  CGImageRef image = source ? CGImageSourceCreateThumbnailAtIndex(source, 0, (__bridge CFDictionaryRef)options) : NULL;
  if (source) CFRelease(source);
  size_t w = image ? CGImageGetWidth(image) : 0;
  size_t h = image ? CGImageGetHeight(image) : 0;
  if (!w || !h || w > 2048 || h > 2048) {
    if (image) CGImageRelease(image);
    lq_photo_publish(&lq_photo, token, 3, 0, 0, NULL, 0);
    return;
  }
  unsigned char* rgba = calloc(w*h, 4);
  CGColorSpaceRef space = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
  CGContextRef context = rgba ? CGBitmapContextCreate(rgba, w, h, 8, w*4, space,
      kCGImageAlphaPremultipliedLast | kCGBitmapByteOrder32Big) : NULL;
  CGColorSpaceRelease(space);
  if (context) {
    CGContextDrawImage(context, CGRectMake(0, 0, w, h), image);
    CGContextRelease(context);
    // The shared attachment encoder expects straight RGBA, not premultiplied.
    for (size_t i = 0; i < w*h; i++) {
      unsigned a = rgba[4*i+3];
      for (int c = 0; c < 3; c++) {
        unsigned v = a ? (rgba[4*i+c]*255u + a/2)/a : 0;
        rgba[4*i+c] = (unsigned char)(v > 255 ? 255 : v);
      }
    }
    lq_photo_publish(&lq_photo, token, 1, (uint32_t)w, (uint32_t)h, rgba, w*h*4);
  } else lq_photo_publish(&lq_photo, token, 3, 0, 0, NULL, 0);
  free(rgba);
  CGImageRelease(image);
}

@implementation LeanPhotoPicker
- (void)picker:(PHPickerViewController*)picker didFinishPicking:(NSArray<PHPickerResult*>*)results {
  uint32_t token = self.token;
  NSItemProvider* provider = results.firstObject.itemProvider;
  // Completion means the composer can open another picker immediately.
  // Publishing cancellation before dismissal completes races a quick retry.
  [picker dismissViewControllerAnimated:YES completion:^{
    if (lq_picker == picker) { lq_picker = nil; lq_picker_delegate = nil; }
    if (!provider) { lq_photo_publish(&lq_photo, token, 2, 0, 0, NULL, 0); return; }
    [provider loadFileRepresentationForTypeIdentifier:@"public.image" completionHandler:^(NSURL* url, NSError* error) {
      // The temporary URL remains valid only during this callback.
      lq_photo_file(token, error ? nil : url);
    }];
  }];
}
@end

lean_obj_res lq_pick_photo(uint32_t token) {
  lq_photo_begin(&lq_photo, token);
  dispatch_async(dispatch_get_main_queue(), ^{
    if (!token) {
      [lq_picker dismissViewControllerAnimated:NO completion:nil];
      lq_picker = nil; lq_picker_delegate = nil;
      return;
    }
    if (!lq_photo_current(&lq_photo, token)) return;
    UIViewController* presenter = lq_root.window.rootViewController;
    if (!presenter || presenter.presentedViewController) {
      lq_photo_publish(&lq_photo, token, 3, 0, 0, NULL, 0);
      return;
    }
    [presenter.view endEditing:YES];
    PHPickerConfiguration* config = [[PHPickerConfiguration alloc] init];
    config.filter = PHPickerFilter.imagesFilter;
    config.selectionLimit = 1;
    config.preferredAssetRepresentationMode = PHPickerConfigurationAssetRepresentationModeCurrent;
    lq_picker = [[PHPickerViewController alloc] initWithConfiguration:config];
    lq_picker_delegate = [LeanPhotoPicker new];
    lq_picker_delegate.token = token;
    lq_picker.delegate = lq_picker_delegate;
    [presenter presentViewController:lq_picker animated:YES completion:nil];
  });
  return lean_io_result_mk_ok(lean_box(true));
}

lean_obj_res lq_photo_result(void) {
  uint32_t header[4]; unsigned char* bytes; size_t size;
  bool ready = lq_photo_take(&lq_photo, header, &bytes, &size);
  lean_object* hdr = lean_mk_empty_array();
  lean_object* px = lean_alloc_sarray(1, size, size);
  if (ready) for (int i = 0; i < 4; i++) hdr = lean_array_push(hdr, lean_box_uint32(header[i]));
  if (size) memcpy(lean_sarray_cptr(px), bytes, size);
  free(bytes);
  lean_object* result = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(result, 0, hdr); lean_ctor_set(result, 1, px);
  return lean_io_result_mk_ok(result);
}
